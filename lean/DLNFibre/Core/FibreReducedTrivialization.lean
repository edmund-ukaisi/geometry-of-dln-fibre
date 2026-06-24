import DLNFibre.Core.MultComorphism
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# `DLNFibre.Core.FibreReducedTrivialization` — route-(b) reducedness via the trivialization

The route-(b) reducedness chain of `G2-3` (thread 17, R2-3), wired against the **trivialization** of
the rank-`r` chart as a hypothesis. The certified pen-and-paper input (thread 16) is that the fibre
ideal `I_E = (mult(Ã) − E)` is **radical** (`F_E = k[Ã]/I_E` **reduced**), for every `N ≥ 1`, every
dimension vector, every target (it depends only on `rank E`). The MECHANISM is that reducedness is
**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
trivialization** `S ≅ₐ[k] R ⊗_k F_E` (endpoint normalization), then **descends** to `F_E` over the
field `k`.

This module supplies, sorry-free and unconditionally, the **two ends of that chain** plus the
**closer that consumes it**, leaving the single open rung — the deep product trivialization `e`
itself, together with the reducedness `IsReduced S` of the chart ring — as an explicit
**hypothesis**, not an asserted fact:

1. **`isReduced_of_tensor`** — the tensor-with-a-field reducedness **descent** `F` reduced ⟸
   `R ⊗_k F` reduced (over a field `k`, any nontrivial `k`-algebra `R`). The "one open dependency"
   the thread-16 certificate flagged; here it is the direct `includeRight` injection
   (`Algebra.TensorProduct.includeRight_injective` + `isReduced_of_injective`), **not** the
   geometric `IsGeometricallyReduced` (which descends in the opposite direction).

2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
   trivialization `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` and `IsReduced S` (the reduced chart ring),
   `R ⊗_k F_E` is reduced (transfer along `e`), hence `F_E` is reduced (descent (1)), hence
   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).

3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
   identity the height-squeeze (R2-5/R2-6, `height m_B = δ`) consumes.

**What is Proved vs Assumed here.** Everything above is proved sorry-free *given* the trivialization
`e : S ≃ₐ[k] R ⊗_k F_B` and `IsReduced S`, which are carried as **explicit hypotheses** — never as a
`sorry` or a global axiom. The deep trivialization `e` itself (the endpoint-normalization product
iso, built from a deep localized chart ring `S = O(Σ̄^r ∩ chart)`) is **not** constructed here: it
is the **open residual `G2-3` wall, R2-3b** (new scheme-free affine scaffolding — no deep localized
total ring exists in the engine yet, G2-2's machinery is `N = 1` only; ~5–8 modules). No downstream
result may claim `codim (fibre) = C + δ` or discharge `BundleShiftInterface` on the strength of
these conditional theorems while `e` is a hypothesis — that discharge waits for R2-3b to prove `e`.
The theorems here are an honest, clearly-labelled *conditional* pre-build of the downstream: every
consumer of `e` is **already proved against the hypothesis**, so R2-3b closes the chain with no
further reducedness work. (Codex's recommended build order for `e` is recorded in the thread's
`codex/algequiv-answer.md`.)

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The fibre coordinate algebra `F_E` -/

/-- The **fibre coordinate algebra** `F_B = k[Ã] / (mult(Ã) − B)`: the coordinate ring of the cut
scheme `mult⁻¹(B)`, i.e. `MvPolynomial (RepCoord d) k` modulo the fibre generator ideal. (`F_E` in
the certificate is this at the rank normal form `B = E`; the construction is uniform in `B`.) -/
abbrev FibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Type u :=
  MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B

/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
`Ideal.isRadical_iff_quotient_reduced` for the fibre algebra. The bridge route-(b) crosses (the
geometric reducedness of `F_B` is exactly the radical-collapse the height-squeeze wants). -/
theorem fibreGenIdeal_isRadical_iff_isReduced_fibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
  Ideal.isRadical_iff_quotient_reduced (fibreGenIdeal d B)

/-! ## The tensor-with-a-field reducedness descent (the pinned dependency)

`F` reduced ⟸ `R ⊗_k F` reduced over a field `k`. Direct via the **injection**
`includeRight : F →ₐ[k] R ⊗_k F` (a nonzero `k`-algebra `R` makes `algebraMap k R` injective, and
`F` is `k`-flat as a vector space, so `includeRight` is injective by
`Algebra.TensorProduct.includeRight_injective`), then `isReduced_of_injective`. This is the standard
char-0 descent the certificate named — but it needs only a field base and a nontrivial `R`. -/

/-- **Tensor-with-a-field reducedness descent.** Over a field `k`, for any nontrivial commutative
`k`-algebra `R` and commutative `k`-algebra `F`: if `R ⊗_k F` is reduced then `F` is reduced. The
injection `F ↪ R ⊗_k F` (`includeRight`, injective since `F` is `k`-flat and `algebraMap k R` is
injective) pulls back reducedness. -/
theorem isReduced_of_tensor {R F : Type u} [CommRing R] [Nontrivial R] [CommRing F]
    [Algebra k R] [Algebra k F] (h : IsReduced (R ⊗[k] F)) : IsReduced F :=
  letI := h
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k R).injective)

/-! ## The route-(b) chain through the trivialization (the open rung as a hypothesis) -/

/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
`S` reduced ⟹ `R ⊗_k F_B` reduced (transfer along `e.symm`) ⟹ `F_B` reduced (`isReduced_of_tensor`)
⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
theorem fibreGenIdeal_isRadical_of_trivialization
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    (fibreGenIdeal d B).IsRadical := by
  letI := hSred
  -- `S` reduced ⟹ `R ⊗ F_B` reduced (it injects into `S` via `e.symm`)
  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
    isReduced_of_injective e.symm.toRingEquiv e.symm.injective
  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)

/-- **The radical-collapse of `MultComorphism` point 4** (through the trivialization). With the cut
ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
identity the height-squeeze (`height m_B = δ`, R2-5/R2-6) consumes. `[IsAlgClosed k]` (the
Nullstellensatz bridge). -/
theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
  rw [vanishingIdeal_image_fibre_eq_radical,
    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]

/-! ## Non-vacuity witnesses

The descent (1) is non-vacuous over any field. The chain (2)/(3) is non-vacuous with `S := R ⊗ F_B`
and the identity equiv `e := AlgEquiv.refl` — exhibiting that the hypotheses are jointly satisfiable
(a reduced `S` admitting the iso), so the conclusions are not vacuously
derived from contradictory hypotheses. -/

section Witness

/-- The tensor-descent fires over `ℚ` (a field) for `R = ℚ`, `F = ℚ`: `ℚ ⊗_ℚ ℚ` reduced ⟹ `ℚ`
reduced — non-vacuous. -/
example (h : IsReduced (ℚ ⊗[ℚ] ℚ)) : IsReduced ℚ := isReduced_of_tensor (k := ℚ) h

/-- The chain's hypotheses are jointly satisfiable: with `S := R ⊗_k F_B`, `R` a nontrivial reduced
domain and `F_B` reduced, the identity equiv `e := AlgEquiv.refl` and `IsReduced S` discharge the
hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
content is the *shape* of the contract; the genuine `e` for the rank chart is the deferred rung.) -/
example [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (R : Type u) [CommRing R] [Nontrivial R]
    [Algebra k R] [IsReduced (R ⊗[k] FibreAlg d B)] :
    (fibreGenIdeal d B).IsRadical :=
  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
    (AlgEquiv.refl) ‹_›

end Witness

end DLNFibre.Core
