import DLNFibre.DLN.RLCT.Validate.RouteMSchurRect

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCharged` — the CHARGED rectangular Schur recursion (SPEC + wrapper)

The charge-carrying generalisation of the banked uncharged `RouteMSchurRect.RectSchurCore` /
`rectCore_schurGen_lt_top`. The terminal core of the item-4 mountain (couplerad §w3): the reduced
bilinear `frobSq(Front·Z_deep)` decorated with the charge `det((A_cor·Z_deep)(A_cor·Z_deep)ᵀ)^{−a/2}`,
with the charge threaded THROUGH the corank recursion at exponent-shift `δ = 0` — the charged per-cell
RLCT-codim EQUALS the uncharged floor `minAdm(![m,n,p])` (couplerad ★4: the charge is FREE in the codim,
but NOT via a loss-fold — the fold is pointwise FALSE `Front ⊥ A_cor`, and δ>0 under-proves on tight
shells; §w3 CORRECTION).

## Shape (corankrec's terminal, option (ii)) — three FREE matrices over radius-`T` boxes

`ChargedRectSchurCore m n p a b c' T` integrates over `Δ ∈ matBox m n T` (the loss's first factor
`Front`, `m×n`), `A_cor ∈ matBox b n T` (the charge's separate matrix, `b×n`), `S ∈ matBox n p T`
(the shared deep factor `Z_deep`, `n×p`); integrand `det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}·frobSq(Δ·S)^{−c'}`.
Maps `(m,n,p) = (u, M₂, n_last)`, `a = M₀−u`, `b = M₁−u`. The loss exponent `c'` is couplerad's `q' =
c'−ab/2` (the `ab/2` Move-1 shift is upstream of this terminal). The threshold is the SAME uncharged
`rectSchurLambda p m n = ½·minAdm(![m,n,p])` — UNSHIFTED (`δ = 0`).

## What is in this file (and what is DEFERRED — the wall)

DETERMINED / SORRY-FREE here (the scaffold, mirroring `RouteMSchurRect` faithfully):
- `chargeGramDet` — the `b×b` Gram determinant `det((A_cor·S)(A_cor·S)ᵀ)` (matches `frontChargeIntegrand`).
- `ChargedRectSchurCore m n p a b c' T` — the charged box-finiteness predicate.
- `ChargedRectSchurLowerIH` / `ChargedRectSchurRecStep` — the charged joint-core IH and the deferred
  per-corank step; the charge exponents `(a, b)` are RECURSION PARAMETERS (fixed), only `(m, n)` and `c'`
  descend, because `Q_b = A_cor·S` stays `b×p` under the shared-middle drop (the Gram is always `b×b` —
  the charge is a fixed `b×b`-Gram decoration throughout, so the rankgen scope is a fixed side-hypothesis).
- `chargedRectCore_schurGen_lt_top` — the WellFounded-on-`min(m,n)` wrapper (the determined part; PROVED,
  reuses the uncharged `RectSchurThreshold` contract — the threshold is charge-agnostic, `δ = 0`).

DEFERRED (the wall, couplerad §w3-percorank, in flight): the charged per-corank step
`ChargedRectSchurRecStep` PROOF — the charged N2b split + the `Matrix.det_fromBlocks`-based Gram
Schur-complement factorisation absorbing the charge exponent at `δ = 0` (Cauchy–Binet-free) + the
banked `corankBlock_morsePeel` charge atom + the a.e.-PosDef `hGae`. It consumes couplerad's exact
per-corank Gram–Schur inequality. This scaffold takes it as the `hstep` HYPOTHESIS, so the wrapper is
sorry-free and axiom-clean; the deferred content is named, not hidden.

## OPEN — the rankgen scope (converging with couplerad)

couplerad §5/§6: off the binding-shell rankgen (`a+b ≤ ρ−1`, `ρ = deepTailMin`) the charge lowers the
codim below the floor, so the `δ=0` claim NEEDS a rankgen hypothesis. Since `(a,b,p)` are
recursion-invariant, this is a FIXED side-hypothesis, carried on the per-corank step + the endpoint
(NOT threaded per-step). Its exact form (`a+b+1 ≤ ?` in `(m,n,p)`) is pinned by couplerad's §w3-percorank
and enters the WALL, not this scaffold — the wrapper below is rankgen-agnostic (it threads whatever
`ChargedRectSchurRecStep` asserts).
-/

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The charge Gram determinant -/

/-- **The charge Gram determinant** `det((A_cor·S)(A_cor·S)ᵀ)` — a `b×b` Gram det (`A_cor : b×n`,
`S : n×p`, so `Q_b := A_cor·S : b×p`). Matches `frontChargeIntegrand`'s
`((hsQ …).submatrix Sum.inr id * (…)ᵀ).det` (`RouteMSJIncidenceAssembly`), where
`(hsQ …).submatrix Sum.inr id = Matrix.of A_cor * Z_deep`. Nonneg (Gram, `PosSemidef.det_nonneg`). -/
noncomputable def chargeGramDet {b n p : ℕ} (Acor : Fin b → Fin n → ℝ) (S : Fin n → Fin p → ℝ) : ℝ :=
  ((Matrix.of (rmatMul Acor S)) * (Matrix.of (rmatMul Acor S))ᵀ).det

/-- **The charge Gram det at `b = 1` is the scalar `frobSq(A_cor·S)`.** The `1×1` Gram
`(A_cor·S)(A_cor·S)ᵀ` has determinant its single entry `∑_j (A_cor·S)_{0j}² = frobSq(A_cor·S)`. Bridges
the `b = 1` charge to the banked `frobSq`-based corank-weight atoms (`corankWeight_lt_top`). -/
theorem chargeGramDet_one {n p : ℕ} (Acor : Fin 1 → Fin n → ℝ) (S : Fin n → Fin p → ℝ) :
    chargeGramDet Acor S = frobSq (rmatMul Acor S) := by
  unfold chargeGramDet frobSq
  rw [Matrix.det_fin_one]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_one]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sq]

/-! ## The charged corank finiteness predicate -/

/-- **The charged rectangular Schur core finiteness predicate.** `ChargedRectSchurCore m n p a b c' T`
asserts the coupled free-box core integral
`∫_{Δ∈matBox m n T} ∫_{A_cor∈matBox b n T} ∫_{S∈matBox n p T}
  det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}·frobSq(Δ·S)^{−c'}` is finite. The charge-carrying generalisation of
`RectSchurCore m n p c' T` (which is the `a = 0` charge-free specialisation, up to the `A_cor` box
volume). Three FREE matrices; `Δ = Front`, `A_cor` the charge's separate matrix, `S = Z_deep` shared. -/
def ChargedRectSchurCore (m n p a b : ℕ) (c' T : ℝ) : Prop :=
  (∫⁻ Δ in matBox m n T, ∫⁻ Acor in matBox b n T, ∫⁻ S in matBox n p T,
      ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2) * (frobSq (rmatMul Δ S)) ^ (-c')))
    < ⊤

/-! ## The charged joint-core IH and the deferred per-corank step -/

/-- **The charged joint-core IH.** At dims `(m,n)`, after the `j`-block peel the residual is the JOINT
free-box charged `(m−j)×(n−j)` core at the SHIFTED loss exponent `c'' = c' − jp/2`, with the SAME charge
exponents `(a, b)` (recursion-invariant — the `b×b` Gram shape is fixed). The charged analog of
`RectSchurLowerIH`. -/
def ChargedRectSchurLowerIH (p a b : ℕ) (lam : ℕ → ℕ → ℝ) (m n : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ m → j ≤ n →
    ∀ c'' : ℝ, 0 < c'' → c'' < lam (m - j) (n - j) →
      ∀ T'' : ℝ, 0 < T'' → ChargedRectSchurCore (m - j) (n - j) p a b c'' T''

/-- **The deferred charged per-corank step (the contract, NOT proved here).** Given the (charge-agnostic)
threshold contract and the charged lower-dim IH, the charged `(m,n)` core is finite below `lam m n`. The
genuine wall: the charged N2b split + `det_fromBlocks` Gram factorisation absorbing the charge at `δ=0` +
the banked `corankBlock_morsePeel` charge atom + `hGae`, recursing on the joint charged lower core. The
wrapper takes it as a HYPOTHESIS — scaffold sorry-free, content named. The charged analog of
`RectSchurRecStep`. (Any rankgen scope hypothesis lives INSIDE the eventual inhabitant of this contract,
converging with couplerad §w3-percorank.) -/
def ChargedRectSchurRecStep (p a b : ℕ) (lam : ℕ → ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, RectSchurThreshold p lam → ChargedRectSchurLowerIH p a b lam m n →
    ∀ c' : ℝ, 0 < c' → c' < lam m n →
      ∀ T : ℝ, 0 < T → ChargedRectSchurCore m n p a b c' T

/-! ## The WellFounded-on-`min(m,n)` wrapper (the determined part — PROVED, sorry-free) -/

/-- **The ∀-`(m,n)` charged finiteness, GIVEN the per-step `recStep`.** Strong induction on the measure
`k = min(m,n)` (the peel drops `(m,n) → (m−j, n−j)` with `j ≥ 1`, so `min(m−j,n−j) < min(m,n)`); the
charge exponents `(a,b)` are fixed recursion parameters. No analytic content lives here — the per-step
work is the `hstep` hypothesis, deferred. The charged analog of `rectCore_schurGen_lt_top`; axiom-clean
(`hstep` a hypothesis; reuses the charge-agnostic `RectSchurThreshold` contract). -/
theorem chargedRectCore_schurGen_lt_top
    (p a b : ℕ) (lam : ℕ → ℕ → ℝ)
    (hlam : RectSchurThreshold p lam)
    (hstep : ChargedRectSchurRecStep p a b lam) :
    ∀ m n : ℕ, ∀ c' : ℝ, 0 < c' → c' < lam m n →
      ∀ T : ℝ, 0 < T → ChargedRectSchurCore m n p a b c' T := by
  suffices H : ∀ k : ℕ, ∀ m n : ℕ, min m n = k → ∀ c' : ℝ, 0 < c' → c' < lam m n →
      ∀ T : ℝ, 0 < T → ChargedRectSchurCore m n p a b c' T by
    intro m n; exact H (min m n) m n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m n hk c' hc0 hclt T hT
    refine hstep m n hlam ?_ c' hc0 hclt T hT
    intro j hj0 hjm hjn c'' hc0' hclam T'' hT''
    exact ih (min (m - j) (n - j)) (by omega) (m - j) (n - j) rfl c'' hc0' hclam T'' hT''

end DLNFibre.DLN.RLCT
