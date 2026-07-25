import DLNFibre.DLN.Aoyagi.ChartTransport
import DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

/-!
# `DLN.Aoyagi.Corank2CoreGenEquivar` — RUNG 5d crux (B): `coreGen` is K-equivariant

The rigorous gate for crux (B): `coreGen dvec eWrap` (the transposed (3,3,4) product entries
`(A₁·A₀)ᵢⱼ`) is **equivariant up-to-index-perm** under the coordinate-permutation group
`K = S₄(output rows i) × S₃(output cols j) × S₃(shared/middle m)`, |K| = 864. For the coordinate
permutation `kSigma α β ρ` built from `(α, β, ρ)`:

  `coreGen dvec eWrap k ∘ permOf (kSigma α β ρ) = coreGen dvec eWrap (kTau α β k)`,

with the induced generator-index permutation `kTau α β : (i,j) ↦ (α i, β j)` (the middle `ρ` acts as
a pure gauge, `π = id`). This is the `hequiv` that `transportChart` consumes.

Confirms sector-count's tripwire: the action genuinely MIXES the A0-block (coords `{0..7,20}`) and the
A1-block (coords `{8..19}`) — `kSigma` permutes within each block via the shared grid structure.

**Route status.** This is the route-AGNOSTIC rigorous gate (numerically verified over all 864 elements).
The transport-APPLICATION over chart334's orbit + atlas wiring is HELD pending the cover reconciliation
(decomp-5b ↔ sector-count on the transversal-cover question).
-/

open MeasureTheory Set Matrix
open DLNFibre.Core DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi

/-! ## §0 — `coreGen` as the transposed product entry -/

/-- `coreGen dvec eWrap k u = (A₁ u · A₀ u)ᵢⱼ` with `(i,j) = finProdFinEquiv.symm k` — the entry form
(`coreGen`'s definition composed with `mult_eWrap`). -/
theorem coreGen_eq_A1A0 (k : Fin (dvec (Fin.last 2) * dvec 0)) (u : Fin 21 → ℝ) :
    coreGen dvec eWrap k u
      = (A1 u * A0 u) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp only [coreGen]
  exact congrFun (congrFun (mult_eWrap u) _) _

/-! ## §1 — the coordinate grid maps -/

/-- The A0-block coordinate of grid cell `(m, j)`: `A₀ = !![u20,u2,u3; u0,u4,u6; u1,u5,u7]`. -/
def a0c : Fin 3 → Fin 3 → Fin 21 := ![![20, 2, 3], ![0, 4, 6], ![1, 5, 7]]

/-- The A1-block coordinate of grid cell `(i, m)`: `A₁ i m = u (8 + 4m + i)`. -/
def a1c : Fin 4 → Fin 3 → Fin 21 := fun i m ↦ ⟨8 + 4 * m.val + i.val, by omega⟩

/-- `A₀ u m j = u (a0c m j)` — `A₀`'s entries ARE the grid coordinates. -/
theorem A0_apply (u : Fin 21 → ℝ) (m j : Fin 3) : A0 u m j = u (a0c m j) := by
  fin_cases m <;> fin_cases j <;> rfl

/-- `A₁ u i m = u (a1c i m)`. -/
theorem A1_apply (u : Fin 21 → ℝ) (i : Fin 4) (m : Fin 3) : A1 u i m = u (a1c i m) := rfl

/-! ## §2 — the layout equiv: `Fin 21 ≃ A0-grid ⊕ A1-grid` -/

/-- The layout function: A0-grid cell `(m,j) ↦ a0c m j`, A1-grid cell `(i,m) ↦ a1c i m`. -/
def kLayoutFun : (Fin 3 × Fin 3) ⊕ (Fin 4 × Fin 3) → Fin 21
  | Sum.inl (m, j) => a0c m j
  | Sum.inr (i, m) => a1c i m

/-- The layout as a bijection `A0-grid ⊕ A1-grid ≃ Fin 21` (9 + 12 = 21, checked by `decide`). -/
noncomputable def kLayout : (Fin 3 × Fin 3) ⊕ (Fin 4 × Fin 3) ≃ Fin 21 :=
  Equiv.ofBijective kLayoutFun (by decide)

@[simp] theorem kLayout_inl (m j : Fin 3) : kLayout (Sum.inl (m, j)) = a0c m j := rfl
@[simp] theorem kLayout_inr (i : Fin 4) (m : Fin 3) : kLayout (Sum.inr (i, m)) = a1c i m := rfl

/-! ## §3 — the K-action `kSigma` and its grid action -/

/-- **The K-action coordinate permutation** from `(α, β, ρ) ∈ S₄ × S₃ × S₃`: on the A0-grid
`(m,j) ↦ (ρ m, β j)` (rows by the shared `ρ`, cols by `β`); on the A1-grid `(i,m) ↦ (α i, ρ m)`
(output rows by `α`, cols by the shared `ρ`). Genuinely MIXES the A0/A1 blocks per the shared `ρ`. -/
noncomputable def kSigma (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 21) :=
  (kLayout.symm.trans (Equiv.sumCongr (Equiv.prodCongr ρ β) (Equiv.prodCongr α ρ))).trans kLayout

/-- `kSigma` on an A0-grid coordinate: `(m,j) ↦ (ρ m, β j)`. -/
theorem kSigma_a0c (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3)) (m j : Fin 3) :
    kSigma α β ρ (a0c m j) = a0c (ρ m) (β j) := by
  have h : kLayout.symm (a0c m j) = Sum.inl (m, j) := kLayout.symm_apply_eq.mpr rfl
  simp only [kSigma, Equiv.trans_apply, h, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.prodCongr_apply, Prod.map_apply, kLayout_inl]

/-- `kSigma` on an A1-grid coordinate: `(i,m) ↦ (α i, ρ m)`. -/
theorem kSigma_a1c (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3)) (i : Fin 4) (m : Fin 3) :
    kSigma α β ρ (a1c i m) = a1c (α i) (ρ m) := by
  have h : kLayout.symm (a1c i m) = Sum.inr (i, m) := kLayout.symm_apply_eq.mpr rfl
  simp only [kSigma, Equiv.trans_apply, h, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.prodCongr_apply, Prod.map_apply, kLayout_inr]

/-! ## §4 — the transported A0/A1 blocks -/

/-- `A₀` under `permOf (kSigma α β ρ)`: rows permuted by `ρ`, cols by `β`. -/
theorem A0_permOf_kSigma (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3)) (u : Fin 21 → ℝ)
    (m j : Fin 3) : A0 (permOf (kSigma α β ρ) u) m j = A0 u (ρ m) (β j) := by
  rw [A0_apply, permOf_apply, kSigma_a0c, A0_apply]

/-- `A₁` under `permOf (kSigma α β ρ)`: output rows permuted by `α`, cols by `ρ`. -/
theorem A1_permOf_kSigma (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3)) (u : Fin 21 → ℝ)
    (i : Fin 4) (m : Fin 3) : A1 (permOf (kSigma α β ρ) u) i m = A1 u (α i) (ρ m) := by
  rw [A1_apply, permOf_apply, kSigma_a1c, A1_apply]

/-- **The product reindexing** — the shared `ρ` cancels in the contraction: the transported product
`(A₁·A₀)` at `(i,j)` equals the original product at `(α i, β j)`. -/
theorem A1A0_permOf_kSigma (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3)) (u : Fin 21 → ℝ)
    (i : Fin 4) (j : Fin 3) :
    (A1 (permOf (kSigma α β ρ) u) * A0 (permOf (kSigma α β ρ) u)) i j
      = (A1 u * A0 u) (α i) (β j) := by
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp ρ (fun m ↦ A1 u (α i) m * A0 u m (β j))]
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  rw [A1_permOf_kSigma, A0_permOf_kSigma]

/-! ## §5 — the generator-index permutation and the equivariance -/

/-- The induced permutation of the generator index `Fin (d_N · d_0)`: `(i,j) ↦ (α i, β j)`. -/
noncomputable def kTau (α : Equiv.Perm (Fin 4)) (β : Equiv.Perm (Fin 3)) :
    Equiv.Perm (Fin (dvec (Fin.last 2) * dvec 0)) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr α β).trans finProdFinEquiv)

theorem kTau_symm (α : Equiv.Perm (Fin 4)) (β : Equiv.Perm (Fin 3))
    (k : Fin (dvec (Fin.last 2) * dvec 0)) :
    finProdFinEquiv.symm (kTau α β k)
      = (α (finProdFinEquiv.symm k).1, β (finProdFinEquiv.symm k).2) := by
  have h : finProdFinEquiv.symm (kTau α β k) = Equiv.prodCongr α β (finProdFinEquiv.symm k) :=
    finProdFinEquiv.symm_apply_apply (Equiv.prodCongr α β (finProdFinEquiv.symm k))
  rw [h]
  rfl

/-- **`coreGen` IS K-equivariant (up to index-perm)** — the crux-(B) gate, RIGOROUS. For any
`(α, β, ρ) ∈ S₄ × S₃ × S₃`, `coreGen k (permOf (kSigma α β ρ) u) = coreGen (kTau α β k) u`: the
coordinate action permutes the transposed product `(A₁·A₀)` by `(α, β)` on its `(row, col)` indices,
the shared `ρ` cancelling in the contraction (`A1A0_permOf_kSigma`). The middle `ρ` acts as a pure
gauge (absent from `kTau`). -/
theorem coreGen_permOf_kSigma (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3))
    (k : Fin (dvec (Fin.last 2) * dvec 0)) (u : Fin 21 → ℝ) :
    coreGen dvec eWrap k (permOf (kSigma α β ρ) u) = coreGen dvec eWrap (kTau α β k) u := by
  rw [coreGen_eq_A1A0, coreGen_eq_A1A0, kTau_symm]
  exact A1A0_permOf_kSigma α β ρ u _ _

/-- **The `hequiv` form** `coreGen`'s K-equivariance takes for `transportChart`:
`∀ k, coreGen k ∘ permOf (kSigma α β ρ) = coreGen (kTau α β k)`. -/
theorem coreGen_comp_permOf_kSigma (α : Equiv.Perm (Fin 4)) (β ρ : Equiv.Perm (Fin 3))
    (k : Fin (dvec (Fin.last 2) * dvec 0)) :
    coreGen dvec eWrap k ∘ permOf (kSigma α β ρ) = coreGen dvec eWrap (kTau α β k) := by
  funext u; exact coreGen_permOf_kSigma α β ρ k u

end DLNFibre.DLN.Aoyagi
