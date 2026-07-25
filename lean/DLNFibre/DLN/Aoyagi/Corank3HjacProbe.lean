import DLNFibre.Core.Aoyagi.PathAtoms
import DLNFibre.Core.Aoyagi.BlockBlowup

/-!
# Corank-3 `hjac`-only probe — the ≥3 elimination stays CLEAN UNIPOTENT (no divide-by-pivot)

The elder's last `unit ≡ 1` verification axis (R1 M1-wide, the RED-FLIP piece). Corank-2
monomialised
the Jacobian to a pure monomial via `jacDet_comp` over unipotent shears (`jacDet_blockShear = 1`)
and
exact-monomial blow-ups (`jacDet_blockBlowupMap`); `unit ≡ 1` DERIVED
(`Corank2ChartJac.gWrap_hjac`).
At corank ≥ 3 the coupling ACCUMULATES (the b's share divisors, F4): the live risk is the RETIRED
fold's **divide-by-pivot** sneaking back — i.e. clearing the 3rd coupled pivot forcing a step that
is
NOT a clean unipotent `blockShear`.

**Verdict: GREEN — no divide-by-pivot.** Two facts, both banked-general and exercised here:

1. **The elimination stays clean unipotent, coupling-INDEPENDENTLY.** `jacDet_blockShear` gives
   `jacDet (blockShear φ) = 1` for ANY `φ` that is differentiable, vanishes on the kept coords, and
   reads only the kept coords — it does NOT look at `φ`'s content, so however the coupling
accumulates
   (bilinear, trilinear, …), each clearing step is det-1 as long as it is a clean `blockShear`.
Hence
   ANY number of successive clean shears telescopes to `jacDet = 1`
(`jacDet_three_successive_shears`,
   general in `D`). The reason clearing at a blown-up pivot IS a clean shear (not a division): the
   blow-up normalises the pivot to a UNIT, so the Schur clear `Xᵢ ↦ Xᵢ − cᵢ·Xₚ` is a polynomial
   SUBTRACTION (`SchurClearTwoSided` — unit-pivot elimination is unipotent shears, Schur complement
   `D − C·B` polynomial, no `A⁻¹`). The `1/(monomial)` wall fires ONLY if a pivot is NOT a unit —
   which the blow-up precludes. (Sympy-checked: 3 successive unit-pivot Schur clears of a coupled
   `3×3` residual are all unipotent and all polynomial — the accumulated coupling lives in the
   polynomial entries, never a denominator.)

2. **A concrete GENUINELY-COUPLED corank-3 clearing shear is clean**
(`corank3_coupled_shear_clean`):
   `shearPhi3` on `Fin 6` clears the residual slots `{3,4,5}` with 3-pivot coupling — including the
   **trilinear** `w₀·w₁·w₂` (the accumulation the elder flags) — reading only the pivot/kept coords
   `{0,1,2}`; it is a clean `blockShear`, so `jacDet = 1`.

**The full corank-3 composite** (`abs_jacDet_g3`): `g3 = blockShear shearPhi3 ∘ bb₂ ∘ bb₁ ∘ bb₀`
(3 pivot blow-ups + the coupled clearing shear) has `|jacDet g3 u| = |u₀|·|u₁|·|u₂|` — a PURE
monomial,
`unit ≡ 1`, exactly the corank-2 `abs_jacDet_gWrap` pattern scaled to corank-3.

RED-FLIP does NOT fire. Scope: this is a faithful minimal MODEL (a genuine 3-pivot-coupled clearing
+
3 blow-ups), not the full flat `(4,4,4)`-chart; the general `jacDet_three_successive_shears` +
`SchurClearTwoSided` are what make it corank-agnostic.

## Main results
- `jacDet_three_successive_shears` — any 3 clean unipotent blockShears telescope to `jacDet = 1`
  (general `D`, coupling-independent).
- `corank3_coupled_shear_clean` — a concrete 3-pivot-coupled clearing shear (incl. trilinear) is
clean.
- `abs_jacDet_g3` — the corank-3 composite has `|jacDet| = |u₀|·|u₁|·|u₂|` (pure monomial, unit ≡
1).
-/

open DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi.Corank3HjacProbe

/-- `blockShear φ` is differentiable when `φ` is (it is `fun u ↦ u + φ u`). -/
private theorem diff_blockShear {D : ℕ} {φ : (Fin D → ℝ) → (Fin D → ℝ)}
    (hφ : Differentiable ℝ φ) : Differentiable ℝ (blockShear φ) := by
  unfold blockShear
  exact differentiable_id.add hφ

/-- `blockBlowupMap S p` is differentiable (from its `HasFDerivAt`). -/
private theorem diff_bb {D : ℕ} (S : Finset (Fin D)) (p : Fin D) :
    Differentiable ℝ (blockBlowupMap S p) :=
  fun w ↦ (hasFDerivAt_blockBlowupMap S p w).differentiableAt

/-! ## 1. The general fact — a chain of clean unipotent blockShears telescopes to `jacDet = 1` -/

/-- **Any 3 successive clean unipotent blockShears telescope to `jacDet = 1`** — GENERAL in `D`,
coupling-INDEPENDENT. Each `φᵢ` clean (differentiable, vanishing on `kᵢ`, reading only `kᵢ`) gives
`jacDet (blockShear φᵢ) = 1` regardless of its content; the chain rule `jacDet_comp` multiplies the
three `1`s. This is the corank-3 (and beyond) elimination: however the coupling accumulates, the
composite of clearing shears is det-1. -/
theorem jacDet_three_successive_shears {D : ℕ}
    (φ₁ φ₂ φ₃ : (Fin D → ℝ) → (Fin D → ℝ)) (k₁ k₂ k₃ : Fin D → Prop)
    (d₁ : Differentiable ℝ φ₁) (hk₁ : ∀ u i, k₁ i → φ₁ u i = 0)
    (hr₁ : ∀ u v : Fin D → ℝ, (∀ i, k₁ i → u i = v i) → φ₁ u = φ₁ v)
    (d₂ : Differentiable ℝ φ₂) (hk₂ : ∀ u i, k₂ i → φ₂ u i = 0)
    (hr₂ : ∀ u v : Fin D → ℝ, (∀ i, k₂ i → u i = v i) → φ₂ u = φ₂ v)
    (d₃ : Differentiable ℝ φ₃) (hk₃ : ∀ u i, k₃ i → φ₃ u i = 0)
    (hr₃ : ∀ u v : Fin D → ℝ, (∀ i, k₃ i → u i = v i) → φ₃ u = φ₃ v)
    (u : Fin D → ℝ) :
    jacDet (blockShear φ₃ ∘ blockShear φ₂ ∘ blockShear φ₁) u = 1 := by
  have D1 : Differentiable ℝ (blockShear φ₁) := diff_blockShear d₁
  have D2 : Differentiable ℝ (blockShear φ₂) := diff_blockShear d₂
  have D3 : Differentiable ℝ (blockShear φ₃) := diff_blockShear d₃
  rw [jacDet_comp u D3.differentiableAt (D2.comp D1).differentiableAt,
    jacDet_comp u D2.differentiableAt D1.differentiableAt,
    jacDet_blockShear φ₃ k₃ d₃ hk₃ hr₃, jacDet_blockShear φ₂ k₂ d₂ hk₂ hr₂,
    jacDet_blockShear φ₁ k₁ d₁ hk₁ hr₁]
  ring

/-! ## 2. A concrete GENUINELY-COUPLED corank-3 clearing shear (incl. the trilinear accumulation) -/

/-- The corank-3 coupled clearing displacement on `Fin 6`: pivots `{0,1,2}` clear the residual slots
`{3,4,5}` with genuine 3-pivot coupling — slot 4 is the **trilinear** `w₀·w₁·w₂` (the accumulation).
Reads only the kept coords `{0,1,2}`; `0` on the kept coords. -/
def shearPhi3 (w : Fin 6 → ℝ) : Fin 6 → ℝ := fun i ↦
  if i = 3 then w 0 * w 1
  else if i = 4 then w 0 * w 1 * w 2
  else if i = 5 then w 0 * w 2 + w 1 * w 2
  else 0

/-- The kept coords: the pivots `{0,1,2}` (the shear reads only these; clears `{3,4,5}`). -/
abbrev keep3 : Fin 6 → Prop := fun i ↦ i.val < 3

/-- `shearPhi3` vanishes on the kept coords. -/
theorem shearPhi3_keep (u : Fin 6 → ℝ) (i : Fin 6) (hi : keep3 i) : shearPhi3 u i = 0 := by
  fin_cases i <;> first | rfl | (exact absurd hi (by decide))

/-- `shearPhi3` reads only the kept coords. -/
theorem shearPhi3_read (u v : Fin 6 → ℝ) (h : ∀ i, keep3 i → u i = v i) :
    shearPhi3 u = shearPhi3 v := by
  funext i
  simp only [shearPhi3]
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide)]

/-- `shearPhi3` is differentiable (each component is a polynomial). -/
theorem differentiable_shearPhi3 : Differentiable ℝ shearPhi3 := by
  refine differentiable_pi.2 (fun i ↦ ?_)
  fin_cases i <;>
    (simp only [shearPhi3, Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] <;> fun_prop)

/-- **The corank-3 coupled clearing shear is CLEAN unipotent** — `jacDet (blockShear shearPhi3) =
1`,
despite the genuine 3-pivot coupling (incl. the trilinear `w₀·w₁·w₂`). The accumulation lives in the
polynomial displacement, never a denominator; `jacDet_blockShear` is coupling-blind. -/
theorem corank3_coupled_shear_clean (u : Fin 6 → ℝ) :
    jacDet (blockShear shearPhi3) u = 1 :=
  jacDet_blockShear shearPhi3 keep3 differentiable_shearPhi3 shearPhi3_keep shearPhi3_read u

/-! ## 3. The full corank-3 composite: `|jacDet g3| = |u₀|·|u₁|·|u₂|` (pure monomial, unit ≡ 1) -/

/-- The three pivot blow-ups (disjoint centers, one per pivot): each contributes `|w_pivot|¹`. -/
def bb0 : (Fin 6 → ℝ) → (Fin 6 → ℝ) := blockBlowupMap ({0, 3} : Finset (Fin 6)) 0
def bb1 : (Fin 6 → ℝ) → (Fin 6 → ℝ) := blockBlowupMap ({1, 4} : Finset (Fin 6)) 1
def bb2 : (Fin 6 → ℝ) → (Fin 6 → ℝ) := blockBlowupMap ({2, 5} : Finset (Fin 6)) 2

/-- The corank-3 composite chart map: 3 pivot blow-ups then the coupled clearing shear. -/
def g3 : (Fin 6 → ℝ) → (Fin 6 → ℝ) := blockShear shearPhi3 ∘ bb2 ∘ bb1 ∘ bb0

/-- Each blow-up's Jacobian is its pivot coordinate (`|center| = 2 ⟹ exponent 1`). -/
private theorem jacDet_bb0 (w : Fin 6 → ℝ) : jacDet bb0 w = w 0 := by
  rw [bb0, jacDet_blockBlowupMap (by decide : (0 : Fin 6) ∈ ({0, 3} : Finset (Fin 6)))]
  norm_num [show ({0, 3} : Finset (Fin 6)).card - 1 = 1 from by decide]

private theorem jacDet_bb1 (w : Fin 6 → ℝ) : jacDet bb1 w = w 1 := by
  rw [bb1, jacDet_blockBlowupMap (by decide : (1 : Fin 6) ∈ ({1, 4} : Finset (Fin 6)))]
  norm_num [show ({1, 4} : Finset (Fin 6)).card - 1 = 1 from by decide]

private theorem jacDet_bb2 (w : Fin 6 → ℝ) : jacDet bb2 w = w 2 := by
  rw [bb2, jacDet_blockBlowupMap (by decide : (2 : Fin 6) ∈ ({2, 5} : Finset (Fin 6)))]
  norm_num [show ({2, 5} : Finset (Fin 6)).card - 1 = 1 from by decide]

/-- **THE corank-3 Jacobian** — `|jacDet g3 u| = |u₀|·|u₁|·|u₂|`, a PURE monomial (`unit ≡ 1`), via
`jacDet_comp` over the atoms: the coupled clearing shear (det 1, `corank3_coupled_shear_clean`) and
the
three exact-monomial blow-ups (`jacDet_blockBlowupMap`, each `|w_pivot|¹`). No unit factor, no
divide-by-pivot — the corank-2 `abs_jacDet_gWrap` pattern at corank-3. -/
theorem abs_jacDet_g3 (u : Fin 6 → ℝ) :
    |jacDet g3 u| = |u 0| * |u 1| * |u 2| := by
  have hbb0_1 : (bb0 u) 1 = u 1 := by simp [bb0, blockBlowupMap]
  have hbb0_2 : (bb0 u) 2 = u 2 := by simp [bb0, blockBlowupMap]
  have hbb1_2 : (bb1 (bb0 u)) 2 = u 2 := by simp [bb1, blockBlowupMap, hbb0_2]
  have dB0 : Differentiable ℝ bb0 := diff_bb ({0, 3} : Finset (Fin 6)) 0
  have dB1 : Differentiable ℝ bb1 := diff_bb ({1, 4} : Finset (Fin 6)) 1
  have dB2 : Differentiable ℝ bb2 := diff_bb ({2, 5} : Finset (Fin 6)) 2
  have dS := diff_blockShear differentiable_shearPhi3
  unfold g3
  rw [jacDet_comp u dS.differentiableAt ((dB2.comp (dB1.comp dB0)).differentiableAt),
    corank3_coupled_shear_clean, one_mul,
    jacDet_comp u dB2.differentiableAt ((dB1.comp dB0).differentiableAt),
    jacDet_comp u dB1.differentiableAt dB0.differentiableAt,
    jacDet_bb2, jacDet_bb1, jacDet_bb0, Function.comp_apply, hbb1_2, hbb0_1, abs_mul, abs_mul]
  ring

end DLNFibre.DLN.Aoyagi.Corank3HjacProbe
