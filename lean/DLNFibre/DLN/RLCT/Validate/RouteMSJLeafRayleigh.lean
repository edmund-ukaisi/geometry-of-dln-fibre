import DLNFibre.DLN.RLCT.Validate.RouteMSJRayleigh
import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJLeafRayleigh` — the Rayleigh matrix bound (route-A base core)

**Thread `genm-sj5-descent`, the A2 `DecoratedBaseHyp` route-A core (controller decision + cover Q4 PASS).**
The decorated width-2 base leaf reduces to the FREE-block Morse via the **Rayleigh matrix bound**: if the
deeper Gram `Z·Zᵀ` dominates `c·I` (`Z·Zᵀ − c·I ≽ 0` — the units-on-chart interface, `#144`-supplied), then

    c · frobSq Γ  ≤  frobSq (Γ · Z).

Hence `(frobSq (Γ·Z))^{−c'} ≤ c^{−c'}·(frobSq Γ)^{−c'}` (`−c' ≤ 0`), and the leaf integral majorises by the
free-`Γ` Morse `∫ (frobSq Γ)^{−c'}` (finite below `dim(Γ)/2 = ½·minAdm(base)`). This BYPASSES `sjLoss_terminal`
+ the `(P)/(T)` gap entirely (cover Q2): the base is consumed by `DecoratedStepHyp`'s IH as a finiteness
`Prop`, route-agnostically (cover Q4), and the jac-monomial decoration factors out separately. The bound is
LOCAL (`Z` fixed, Loewner-exact) — distinct from the `#140`-killed global-decoupling route.

Proof: `frobSq (Γ·Z) − c·frobSq Γ = trace(Γ·(Z·Zᵀ − c·I)·Γᵀ) ≥ 0`, since `Γ·(PSD)·Γᵀ` is PSD (conjugation,
`PosSemidef.mul_mul_conjTranspose_same`) and PSD-trace `≥ 0` (`PosSemidef.trace_nonneg`); `frobSq = trace(·ᵀ)`
is the banked `frobSq_eq_trace`.

Network-free matrix spectral algebra; consumes only banked `frobSq_eq_trace` + Mathlib PSD. Untracked (A2
co-audited with cover). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {a n D : ℕ}

/-- **The Rayleigh matrix bound (route-A base core).** If `Z·Zᵀ − c·I` is positive semidefinite (the deeper
Gram dominates `c·I`; the units-on-chart interface), then `c · frobSq Γ ≤ frobSq (Γ · Z)`. The difference is
`trace(Γ·(Z·Zᵀ − c·I)·Γᵀ) ≥ 0` (conjugation of a PSD matrix, PSD trace nonneg). No eigenvalues, no `c > 0`
needed for the bound itself. -/
theorem frobSq_mul_ge (Γ : Matrix (Fin a) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin D) ℝ) (c : ℝ)
    (hZ : (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    c * frobSq Γ ≤ frobSq (Γ * Z) := by
  have hconj : (Γ * (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)) * Γᵀ).PosSemidef := by
    have h := hZ.mul_mul_conjTranspose_same Γ
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have htr := hconj.trace_nonneg
  have hkey : (Γ * (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)) * Γᵀ).trace
      = frobSq (Γ * Z) - c * frobSq Γ := by
    rw [frobSq_eq_trace (Γ * Z), frobSq_eq_trace Γ, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.trace_sub]
    congr 1
    · rw [Matrix.transpose_mul]
      congr 1
      simp only [Matrix.mul_assoc]
    · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [hkey] at htr
  linarith

/-- **The Rayleigh bound as a value majorant on the non-degenerate locus.** With `c > 0`, `Z·Zᵀ ≽ c·I`,
and `Γ ≠ 0` (`0 < frobSq Γ`), the leaf loss to a nonpositive power is dominated:
`(frobSq (Γ·Z))^{−c'} ≤ c^{−c'} · (frobSq Γ)^{−c'}` for `0 ≤ c'`. (`{frobSq Γ = 0}` is the single point
`Γ = 0`, measure zero, so this a.e. majorant is what the leaf integral integrates against the free-`Γ`
Morse.) -/
theorem frobSq_mul_rpow_le (Γ : Matrix (Fin a) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin D) ℝ) (c : ℝ)
    (hc : 0 < c) (hZ : (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (c' : ℝ) (hc0 : 0 ≤ c') (hΓ : 0 < frobSq Γ) :
    (frobSq (Γ * Z)) ^ (-c') ≤ c ^ (-c') * (frobSq Γ) ^ (-c') := by
  have hge : c * frobSq Γ ≤ frobSq (Γ * Z) := frobSq_mul_ge Γ Z c hZ
  have hcf : 0 < c * frobSq Γ := mul_pos hc hΓ
  calc (frobSq (Γ * Z)) ^ (-c')
      ≤ (c * frobSq Γ) ^ (-c') := Real.rpow_le_rpow_of_nonpos hcf hge (neg_nonpos.mpr hc0)
    _ = c ^ (-c') * (frobSq Γ) ^ (-c') := Real.mul_rpow hc.le (frobSq_nonneg _)

end DLNFibre.DLN.RLCT
