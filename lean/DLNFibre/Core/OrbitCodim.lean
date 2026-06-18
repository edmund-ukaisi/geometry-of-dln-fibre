import DLNFibre.Core.OrbitLinearCodim
import DLNFibre.Core.IntervalModule
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Height

/-!
# `DLNFibre.Core.OrbitCodim` — the geometric orbit codimension, modulo Voigt (Phase B, hybrid)

The **geometric** codimension of the `G_d`-orbit closure inside `Rep_d`, delivered in
defined-objects form **modulo one named, dischargeable hypothesis** (`hVoigt`). Phase A proved the
*algebraic* / tangent codimension `orbitLinearCodim M = dim Ext¹(M,M) = Σ m_{i-1,j-1} m_{uv}`
(`OrbitLinearCodim`); the geometric equality `codim Ō_M = orbitLinearCodim M` is Voigt's theorem,
whose Lean discharge is a separate algebraic-geometry sub-expedition. Here we:

1. name the orbit closure concretely as the **rank locus** `orbitRankLocus M` (Lehalleur–Rimányi
   2024 Thm 3.8: for the equioriented type-`A` quiver the `G_d`-orbit closure of `M` is exactly the
   determinantal locus `{A | rankPattern A ≤ rankPattern M pointwise}`; **CITED**, not proved here);
2. define the geometric codimension `codimRep` of a closed subset of `Rep_d` as the **height of its
   vanishing ideal** in the coordinate polynomial ring (`Ideal.height ∘ vanishingIdeal`, the
   standard affine codimension; faithful as the codimension of the locus' Zariski closure);
3. state the headline conditionally on `hVoigt : codimRep _ (orbitRankLocus M) = orbitLinearCodim M`
   — **Voigt's lemma**, the single open obligation, an explicit hypothesis (NOT a global `axiom`).

**Name = content.** Nothing here proves the geometry: `orbitRankLocus` is the orbit closure *by the
cited Thm 3.8*; `hVoigt` is *assumed*. The headline `codimRep_orbitRankLocus_eq_multSum` is
**Proved modulo `hVoigt`** — given Voigt, the geometric codimension is the paper's quadratic form,
by `orbitLinearCodim_eq_multSum`. The math is verified exact on `(2,2,2)` (codim `Ō` = dim `Ext¹` =
`3,4,4,8`; rankloc-probe, KMS rectangle sum, prime/normal/CM locus — see `synthesis.md`).

**`codimRep` faithfulness.** `codimRep coord Z := (vanishingIdeal k (coord '' Z)).height`: the
codimension of the Zariski closure of `coord '' Z`, read through a coordinatisation
`coord : Rep_d ≃ (RepCoord d → k)`. The geometric codimension is the height read through the
**canonical linear flattening** (one coordinate per matrix entry); for a *linear* `coord` the height
is coordinate-independent (invariant under the induced ring automorphism). `coord` is left a
parameter — the headline is the honest implication "for this `coord`, given `hVoigt`, …"; the future
Voigt discharge fixes the canonical flattening, at which `hVoigt` is Voigt's lemma. (An
unconstrained set-bijection `coord` need not preserve height; `hVoigt` is only expected/true at the
canonical linear one, and the theorem asserts nothing when `hVoigt` fails.) Definition only — none
of the deep dimension theorems (catenary `dim R/I = n − ht I`, determinantal height, Nullstellensatz
radical bridge) are invoked; those are the `voigt` sub-expedition. `Ideal.height : ℕ∞`, locus codim
is `ℕ∞`-valued.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix Module MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The orbit closure as the rank locus (Lehalleur–Rimányi Thm 3.8, cited) -/

/-- The **rank locus** of `M`: `{A | ∀ i ≤ j, rankPattern A i j ≤ rankPattern M i j}`, the explicit
determinantal subset of `Rep_d` cut out by the rank conditions on the interval sub-products. For the
equioriented type-`A` quiver this is exactly the `G_d`-orbit closure `Ō_M` (Lehalleur–Rimányi 2024
Thm 3.8; **CITED**, not proved here — it is the engine-verifiable orbit-closure-order fact). -/
def orbitRankLocus {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) : Set (Tuple (k := k) d) :=
  {A | ∀ i j (h : i ≤ j), rankPattern d A i j h ≤ rankPattern d M i j h}

/-- `M` lies in its own rank locus (the orbit closure contains the orbit): `rankPattern M ≤
rankPattern M` pointwise. The locus is inhabited — non-vacuity of `orbitRankLocus`. -/
theorem self_mem_orbitRankLocus {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    M ∈ orbitRankLocus M := fun _ _ _ ↦ le_rfl

/-! ## The geometric codimension `codimRep` of a closed subset of `Rep_d`

The standard affine codimension: coordinatise `Rep_d` as the function space `RepCoord d → k`, take
the vanishing ideal of (the image of) the closed subset in `MvPolynomial (RepCoord d) k`, and read
its `Ideal.height`. This is the codimension of the subset's Zariski closure. Definition only. -/

/-- The coordinate index of `Rep_d`: one coordinate per matrix entry,
`(i : Fin N) × Fin (d i.succ) × Fin (d i.castSucc)` — so `Rep_d ≅ RepCoord d → k`. -/
abbrev RepCoord (d : Fin (N + 1) → ℕ) : Type :=
  Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)

instance (d : Fin (N + 1) → ℕ) : Finite (RepCoord d) := by
  unfold RepCoord; infer_instance

/-- The **geometric codimension** of a subset `Z ⊆ Rep_d`, read through a coordinatisation
`coord : Rep_d ≃ (RepCoord d → k)`: the `Ideal.height` of the vanishing ideal of `coord '' Z` in the
coordinate polynomial ring — the standard codimension of the Zariski closure of `coord '' Z`.
Definition only (no dimension theorem invoked). `coord` is a parameter the Voigt discharge fixes to
the **canonical linear flattening** (one coordinate per matrix entry), at which the height is the
genuine geometric codimension; an unconstrained set-bijection need not preserve it, so the headline
is stated for the supplied `coord` + `hVoigt`. `ℕ∞`-valued (`Ideal.height : ℕ∞`). -/
noncomputable def codimRep {d : Fin (N + 1) → ℕ} (coord : Tuple (k := k) d ≃ (RepCoord d → k))
    (Z : Set (Tuple (k := k) d)) : ℕ∞ :=
  Ideal.height
    (MvPolynomial.vanishingIdeal (σ := RepCoord d) (k := k) (K := k) (coord '' Z))

/-! ## The conditional headline — geometric codim = Cor 3.5 quadratic form, modulo Voigt

`hVoigt` is **Voigt's lemma**: the geometric codimension of the orbit closure equals the tangent /
expected codimension `orbitLinearCodim M = dim Ext¹(M,M)`. It is an explicit hypothesis (the single
open obligation, to be discharged by the AG sub-expedition), NOT a global axiom. Given it, the
headline is `orbitLinearCodim_eq_multSum` cast through `ENat.toNat`. -/

/-- **Geometric codim = expected codim, modulo Voigt (`ℕ∞` form).** Restatement of `hVoigt` for
direct use: the geometric codimension of the orbit closure equals the dimension of `Ext¹(M,M)`. The
content is entirely in the assumed `hVoigt` (Voigt's lemma); this just names it against the engine's
`orbitLinearCodim_eq_finrank_deformationExt1`. -/
theorem codimRep_orbitRankLocus_eq_finrank_deformationExt1 {d : Fin (N + 1) → ℕ}
    (coord : Tuple (k := k) d ≃ (RepCoord d → k)) (M : Tuple (k := k) d)
    (hVoigt : codimRep coord (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)) :
    codimRep coord (orbitRankLocus M) = (finrank k (deformationExt1 M M) : ℕ∞) := by
  rw [hVoigt, orbitLinearCodim_eq_finrank_deformationExt1]

/-- **The geometric-codimension headline (Lehalleur–Rimányi Cor 3.5), modulo Voigt.** For
`M = ⊕_{(a,b)∈L} M_{ab}` the geometric codimension of the orbit closure `Ō_M` (the rank locus, Thm
3.8 cited) equals the paper's quadratic form `Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}` — **given Voigt's
lemma `hVoigt`** (geometric codim = expected codim `orbitLinearCodim`). Proved from `hVoigt` +
`orbitLinearCodim_eq_multSum`, casting the `ℕ∞`-valued height to `ℤ` via `ENat.toNat`. The
geometry's only open input is `hVoigt`; everything else is the committed engine. -/
theorem codimRep_orbitRankLocus_eq_multSum (L : List (Fin (N + 1) × Fin (N + 1)))
    (coord : Tuple (k := k) (foldDim L) ≃ (RepCoord (foldDim L) → k))
    (hVoigt : codimRep coord (orbitRankLocus (intervalDirectSum (k := k) L))
      = (orbitLinearCodim (intervalDirectSum (k := k) L) : ℕ∞)) :
    ((codimRep coord (orbitRankLocus (intervalDirectSum (k := k) L))).toNat : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i - 1) (j - 1) * multiplicityArray L u v := by
  rw [hVoigt, ENat.toNat_coe, ← orbitLinearCodim_eq_multSum (k := k)]

end DLNFibre.Core
