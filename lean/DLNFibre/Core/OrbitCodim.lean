import DLNFibre.Core.OrbitLinearCodim
import DLNFibre.Core.IntervalModule
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Height

/-!
# `DLNFibre.Core.OrbitCodim` — the geometric orbit codimension, conditional on Voigt (Phase B, hybrid)

The **geometric** codimension of the `G_d`-orbit closure inside `Rep_d`, delivered in
defined-objects form, stated here in implication form against a named hypothesis (`hVoigt`). Phase A
proved the *algebraic* / tangent codimension `orbitLinearCodim M = dim Ext¹(M,M) = Σ m_{i-1,j-1} m_{uv}`
(`OrbitLinearCodim`); the geometric equality `codim Ō_M = orbitLinearCodim M` is Voigt's theorem,
**now PROVED in the engine** (`Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim`, char 0,
via the dimension squeeze + L7; no algebraic closedness). Here we:

1. name the orbit closure concretely as the **rank locus** `orbitRankLocus M` (Lehalleur–Rimányi
   2024 Thm 3.8: for the equioriented type-`A` quiver the `G_d`-orbit closure of `M` is exactly the
   determinantal locus `{A | rankPattern A ≤ rankPattern M pointwise}`). Thm 3.8 is **PROVED in the
   engine** (zero-cited): the ideal-level identity `Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet`
   and the set-level `Core.OrbitClosure.image_orbitRankLocus_eq_repClosure_orbitSet` (over `[Infinite k]`,
   the hard `≥` by the box-move degeneration);
2. define the geometric codimension `codimRep` of a closed subset of `Rep_d` as the **height of its
   vanishing ideal** in the coordinate polynomial ring (`Ideal.height ∘ vanishingIdeal`, the
   standard affine codimension; faithful as the codimension of the locus' Zariski closure);
3. state the headline in implication form against `hVoigt : codimRep _ (orbitRankLocus M) =
   orbitLinearCodim M` — **Voigt's lemma**, an explicit hypothesis (NOT a global `axiom`). The
   unconditional versions, with `hVoigt` discharged, live in `Core.VoigtDischarge`
   (`codimRepCanonical_orbitRankLocus_eq_multSum_unconditional`).

**Name = content.** The geometry that this module's theorems take as input — `orbitRankLocus = Ō_M`
(Thm 3.8) and Voigt's lemma `hVoigt` — is PROVED elsewhere in `Core` (`OrbitClosure`,
`VoigtDischarge`); the theorems *here* remain stated as honest implications "for this `coord`, given
`hVoigt`, …", and the discharge that removes `hVoigt` is in `VoigtDischarge`. The headline
`codimRep_orbitRankLocus_eq_multSum` is **Proved modulo `hVoigt`** — given Voigt, the geometric
codimension is the paper's quadratic form, by `orbitLinearCodim_eq_multSum`. The math is verified
exact on `(2,2,2)` (codim `Ō` = dim `Ext¹` = `3,4,4,8`; rankloc-probe, KMS rectangle sum,
prime/normal/CM locus — see `synthesis.md`).

**`codimRep` faithfulness.** `codimRep coord Z := (vanishingIdeal k (coord '' Z)).height`: the
codimension of the Zariski closure of `coord '' Z`, read through a coordinatisation
`coord : Rep_d ≃ (RepCoord d → k)`. The geometric codimension is the height read through the
**canonical linear flattening** `canonicalCoord d` (one coordinate per matrix entry,
`A ↦ fun ⟨i, r, c⟩ ↦ A i r c`), now constructed below from `Equiv.curry`/`Equiv.piCurry`. The
geometric headlines are also stated at `canonicalCoord d` directly (`…_canonical` variants and
`codimRepCanonical`), so their `hVoigt` reads `codimRep (canonicalCoord d) (orbitRankLocus M) =
orbitLinearCodim M` — Voigt's lemma at THE canonical flattening, not an arbitrary set-equiv. The
general `codimRep coord …` theorems are kept as honest implications "for this `coord`, given
`hVoigt`, …" — `codimRep` is an honest general building block (any `coord`), and the canonical
specialisation is what the Voigt discharge supplies (`Core.VoigtDischarge`). (An unconstrained set-bijection `coord`
need not preserve height; `hVoigt` is only expected/true at the canonical linear one, and the
theorem asserts nothing when `hVoigt` fails.) **Linear-coordinate invariance** holds for any
*linear* re-coordinatisation: the height agrees with the canonical one (invariant under the induced
ring automorphism of `MvPolynomial (RepCoord d) k`), via (i) the `AlgEquiv` of the coordinate change
on `MvPolynomial`, (ii) `vanishingIdeal (φ ∘ coord '' Z) = comap φ (vanishingIdeal (coord '' Z))`,
and (iii) `(comap φ I).height = I.height` for `φ` a ring iso (`RingEquiv.height_comap`, available at
this pin). For the base-change family of linear isos this is PROVED in
`Core.FibreNormalForm.codimRep_baseChange_image`. This file is definition only — none of the deep
dimension theorems (catenary `dim R/I = n − ht I`, determinantal height, Nullstellensatz radical
bridge) are invoked here. `Ideal.height : ℕ∞`, locus codim is `ℕ∞`-valued.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix Module MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The orbit closure as the rank locus (Lehalleur–Rimányi Thm 3.8, proved in `OrbitClosure`) -/

/-- The **rank locus** of `M`: `{A | ∀ i ≤ j, rankPattern A i j ≤ rankPattern M i j}`, the explicit
determinantal subset of `Rep_d` cut out by the rank conditions on the interval sub-products. For the
equioriented type-`A` quiver this is exactly the `G_d`-orbit closure `Ō_M` (Lehalleur–Rimányi 2024
Thm 3.8). **PROVED in the engine** (zero-cited): the ideal-level
`Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet` and set-level
`Core.OrbitClosure.image_orbitRankLocus_eq_repClosure_orbitSet` (over `[Infinite k]`). -/
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

/-- The **canonical linear flattening** `Rep_d ≃ (RepCoord d → k)`, one coordinate per matrix entry:
`A ↦ fun ⟨i, r, c⟩ ↦ (A i) r c`. Assembled from `Equiv.curry` (each `Matrix … ↔ (… × … → k)`) and
`Equiv.piCurry` (Sigma-currying `∀ i, (… × … → k) ↔ (RepCoord d → k)`). This is the coordinatisation
at which `codimRep` is the genuine geometric codimension. -/
noncomputable def canonicalCoord (d : Fin (N + 1) → ℕ) :
    Tuple (k := k) d ≃ (RepCoord d → k) :=
  (Equiv.piCongrRight (fun i : Fin N ↦
      (Equiv.curry (Fin (d i.succ)) (Fin (d i.castSucc)) k).symm)).trans
    (Equiv.piCurry (fun (_ : Fin N) (_ : Fin (d _) × Fin (d _)) ↦ k)).symm

omit [Field k] in
/-- `canonicalCoord` is the entry-flattening: the coordinate `⟨i, r, c⟩` of `A` is `(A i) r c`. -/
@[simp] theorem canonicalCoord_apply {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d)
    (x : RepCoord d) : canonicalCoord d A x = A x.1 x.2.1 x.2.2 := rfl

/-- The **geometric codimension** of a subset `Z ⊆ Rep_d`, read through a coordinatisation
`coord : Rep_d ≃ (RepCoord d → k)`: the `Ideal.height` of the vanishing ideal of `coord '' Z` in the
coordinate polynomial ring — the standard codimension of the Zariski closure of `coord '' Z`.
Definition only (no dimension theorem invoked). `coord` is a parameter the Voigt discharge
(`Core.VoigtDischarge`) fixes to the **canonical linear flattening** (one coordinate per matrix
entry), at which the height is the genuine geometric codimension; an unconstrained set-bijection need
not preserve it, so the headline is stated for the supplied `coord` + `hVoigt`. `ℕ∞`-valued
(`Ideal.height : ℕ∞`). -/
noncomputable def codimRep {d : Fin (N + 1) → ℕ} (coord : Tuple (k := k) d ≃ (RepCoord d → k))
    (Z : Set (Tuple (k := k) d)) : ℕ∞ :=
  Ideal.height
    (MvPolynomial.vanishingIdeal (σ := RepCoord d) (k := k) (K := k) (coord '' Z))

/-- The geometric codimension of `Z ⊆ Rep_d` at the **canonical linear flattening**
`canonicalCoord d` — the genuine geometric codimension (height of `Z`'s vanishing ideal in the
coordinate ring, one variable per matrix entry). `codimRep` specialised to the canonical coord. -/
noncomputable def codimRepCanonical {d : Fin (N + 1) → ℕ} (Z : Set (Tuple (k := k) d)) : ℕ∞ :=
  codimRep (canonicalCoord d) Z

/-! ## The conditional headline — geometric codim = Cor 3.5 quadratic form, modulo Voigt

`hVoigt` is **Voigt's lemma**: the geometric codimension of the orbit closure equals the tangent /
expected codimension `orbitLinearCodim M = dim Ext¹(M,M)`. It enters these theorems as an explicit
hypothesis (NOT a global axiom). `hVoigt` is **PROVED in the engine**
(`Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim`, char 0; no algebraic closedness);
the unconditional headlines that supply it live in `Core.VoigtDischarge`. The theorems below keep
their implication form (input `hVoigt`, conclude the Cor 3.5 form); given `hVoigt`, the headline is
`orbitLinearCodim_eq_multSum` cast through `ENat.toNat`. -/

/-- **Geometric codim = expected codim, modulo Voigt (`ℕ∞` form).** Restatement of `hVoigt` for
direct use: the geometric codimension of the orbit closure equals the dimension of `Ext¹(M,M)`. The
content is in the supplied `hVoigt` (Voigt's lemma — PROVED in `Core.VoigtDischarge`); this names it
against the engine's `orbitLinearCodim_eq_finrank_deformationExt1`. -/
theorem codimRep_orbitRankLocus_eq_finrank_deformationExt1 {d : Fin (N + 1) → ℕ}
    (coord : Tuple (k := k) d ≃ (RepCoord d → k)) (M : Tuple (k := k) d)
    (hVoigt : codimRep coord (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)) :
    codimRep coord (orbitRankLocus M) = (finrank k (deformationExt1 M M) : ℕ∞) := by
  rw [hVoigt, orbitLinearCodim_eq_finrank_deformationExt1]

/-- **The geometric-codimension headline (Lehalleur–Rimányi Cor 3.5), modulo Voigt.** For
`M = ⊕_{(a,b)∈L} M_{ab}` the geometric codimension of the orbit closure `Ō_M` (the rank locus, Thm
3.8, PROVED in `Core.OrbitClosure`) equals the paper's quadratic form `Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1}
m_{uv}` — **given Voigt's lemma `hVoigt`** (geometric codim = expected codim `orbitLinearCodim`).
Proved from `hVoigt` + `orbitLinearCodim_eq_multSum`, casting the `ℕ∞`-valued height to `ℤ` via
`ENat.toNat`. `hVoigt` is discharged in `Core.VoigtDischarge`
(`codimRepCanonical_orbitRankLocus_eq_multSum_unconditional`); everything else is the committed engine. -/
theorem codimRep_orbitRankLocus_eq_multSum (L : List (Fin (N + 1) × Fin (N + 1)))
    (coord : Tuple (k := k) (foldDim L) ≃ (RepCoord (foldDim L) → k))
    (hVoigt : codimRep coord (orbitRankLocus (intervalDirectSum (k := k) L))
      = (orbitLinearCodim (intervalDirectSum (k := k) L) : ℕ∞)) :
    ((codimRep coord (orbitRankLocus (intervalDirectSum (k := k) L))).toNat : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i - 1) (j - 1) * multiplicityArray L u v := by
  rw [hVoigt, ENat.toNat_coe, ← orbitLinearCodim_eq_multSum (k := k)]

/-! ## The canonical-coordinate headlines — `hVoigt` at THE canonical flattening

The same two headlines, stated at `canonicalCoord d` so the `hVoigt` hypothesis is Voigt's lemma at
the genuine geometric coordinatisation (one variable per matrix entry), not at an arbitrary
set-equiv. These are the statements the Voigt discharge supplies (`Core.VoigtDischarge`); they are
direct specialisations of the general theorems, so they inherit the same proofs. -/

/-- **Geometric codim = expected codim at the canonical flattening, modulo Voigt (`ℕ∞` form).**
`codimRep_orbitRankLocus_eq_finrank_deformationExt1` specialised to `coord = canonicalCoord d`: the
canonical geometric codimension of the orbit closure equals `dim Ext¹(M,M)`, given Voigt's lemma at
the canonical flattening. -/
theorem codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1 {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d)
    (hVoigt : codimRep (canonicalCoord d) (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)) :
    codimRepCanonical (orbitRankLocus M) = (finrank k (deformationExt1 M M) : ℕ∞) :=
  codimRep_orbitRankLocus_eq_finrank_deformationExt1 (canonicalCoord d) M hVoigt

/-- **The geometric-codimension headline (Lehalleur–Rimányi Cor 3.5) at the canonical flattening,
modulo Voigt.** `codimRep_orbitRankLocus_eq_multSum` specialised to `coord = canonicalCoord (foldDim
L)`: the canonical geometric codimension of `Ō_M` equals the paper's quadratic form, given Voigt's
lemma `hVoigt` at THE canonical flattening (one variable per matrix entry). -/
theorem codimRepCanonical_orbitRankLocus_eq_multSum (L : List (Fin (N + 1) × Fin (N + 1)))
    (hVoigt : codimRep (canonicalCoord (foldDim L))
        (orbitRankLocus (intervalDirectSum (k := k) L))
      = (orbitLinearCodim (intervalDirectSum (k := k) L) : ℕ∞)) :
    ((codimRepCanonical (orbitRankLocus (intervalDirectSum (k := k) L))).toNat : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i - 1) (j - 1) * multiplicityArray L u v :=
  codimRep_orbitRankLocus_eq_multSum L (canonicalCoord (foldDim L)) hVoigt

end DLNFibre.Core
