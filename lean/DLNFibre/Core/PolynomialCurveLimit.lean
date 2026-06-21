import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# `DLNFibre.Core.PolynomialCurveLimit` — the one-parameter limit lemma (L6.0)

A **polynomial curve**'s `t = 0` limit lies in the Zariski closure of any subset it lands in for
`t ≠ 0`. Concretely: fix an index type `σ` and an infinite field `k`. A curve is given
coordinate-wise by a family of univariate polynomials `c : σ → k[X]`, and its point at parameter `t`
is `pt c t : σ → k := fun x ↦ (c x).eval t`. If `pt c t ∈ Z` for every `t ≠ 0`, then the limit
point `pt c 0` lies in `zeroLocus (vanishingIdeal Z)` — the Zariski closure of `Z`. Equivalently,
every polynomial vanishing on `Z` also vanishes at `pt c 0`.

The argument is the elementary one: for a fixed `g ∈ vanishingIdeal Z`, substituting the curve into
`g` produces a single univariate polynomial `P_g := aeval c g : k[X]`. Evaluating `P_g` at `t`
commutes with evaluating `g` at `pt c t` (`eval_aeval_curve`), so `P_g.eval t = 0` for every
`t ≠ 0` (because `pt c t ∈ Z` and `g` vanishes on `Z`). The root set of `P_g` thus contains the
complement of `{0}`, which is infinite over an infinite field; hence `P_g = 0`
(`eq_zero_of_infinite_isRoot`), so `P_g.eval 0 = 0`, i.e. `g` vanishes at `pt c 0`.

`[Infinite k]` is the only field hypothesis (it is the weakest that makes the root argument work; an
algebraically closed field is automatically infinite). `σ` need not be finite. Network-free,
reusable engine — the degeneration step (L6) substitutes an explicit polynomial family for `c`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Polynomial

namespace DLNFibre.Core

variable {k : Type*} [Field k] {σ : Type*}

/-- The point of the polynomial curve `c : σ → k[X]` at parameter `t`: coordinate `x` is
`(c x).eval t`. -/
def curvePoint (c : σ → Polynomial k) (t : k) : σ → k := fun x ↦ (c x).eval t

@[simp] theorem curvePoint_apply (c : σ → Polynomial k) (t : k) (x : σ) :
    curvePoint c t x = (c x).eval t := rfl

/-- **Evaluation commutes with curve substitution.** Substituting the curve `c` into `g`
(`aeval c g : k[X]`) and then evaluating at `t` equals evaluating `g` at the curve point `curvePoint
c t`: `(aeval c g).eval t = MvPolynomial.eval (curvePoint c t) g`. -/
theorem eval_aeval_curve (c : σ → Polynomial k) (t : k) (g : MvPolynomial σ k) :
    Polynomial.eval t (MvPolynomial.aeval c g) = MvPolynomial.eval (curvePoint c t) g := by
  rw [MvPolynomial.aeval_eq_eval₂Hom, ← Polynomial.coe_evalRingHom,
    MvPolynomial.map_eval₂Hom (algebraMap k (Polynomial k)) c (Polynomial.evalRingHom t) g]
  have hcomp : (Polynomial.evalRingHom t).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext a; simp
  rw [hcomp]; rfl

/-- **L6.0 — the one-parameter limit lemma.** Over an infinite field `k`, if the polynomial curve
`c : σ → k[X]` lands in `Z ⊆ (σ → k)` for every nonzero parameter, then its `t = 0` limit lies in
the Zariski closure of `Z`: `curvePoint c 0 ∈ zeroLocus (vanishingIdeal Z)`. -/
theorem curvePoint_zero_mem_zeroLocus_vanishingIdeal [Infinite k]
    (c : σ → Polynomial k) (Z : Set (σ → k))
    (hZ : ∀ t : k, t ≠ 0 → curvePoint c t ∈ Z) :
    curvePoint c 0 ∈ zeroLocus k (vanishingIdeal k Z) := by
  rw [MvPolynomial.mem_zeroLocus_iff]
  intro g hg
  -- `aeval c g` has every nonzero `t` as a root: `g` vanishes at `curvePoint c t ∈ Z`.
  have hroot : ∀ t : k, t ≠ 0 → (MvPolynomial.aeval c g).IsRoot t := by
    intro t ht
    rw [Polynomial.IsRoot.def, eval_aeval_curve, ← MvPolynomial.aeval_eq_eval]
    exact (MvPolynomial.mem_vanishingIdeal_iff).mp hg _ (hZ t ht)
  -- The root set contains the infinite set `{0}ᶜ`, so `aeval c g = 0`.
  have hzero : MvPolynomial.aeval c g = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Finite.infinite_compl (Set.finite_singleton (0 : k))).mono
      (fun t ht ↦ hroot t ht)
  -- Hence `g` vanishes at the limit point `curvePoint c 0`.
  change MvPolynomial.eval (curvePoint c 0) g = 0
  rw [← eval_aeval_curve, hzero, Polynomial.eval_zero]

/-- **L6.0, unfolded.** Restatement of `curvePoint_zero_mem_zeroLocus_vanishingIdeal`: every
polynomial `g` vanishing on `Z` also vanishes at the limit point `curvePoint c 0`. -/
theorem aeval_curvePoint_zero_eq_zero_of_mem_vanishingIdeal [Infinite k]
    (c : σ → Polynomial k) (Z : Set (σ → k))
    (hZ : ∀ t : k, t ≠ 0 → curvePoint c t ∈ Z)
    {g : MvPolynomial σ k} (hg : g ∈ vanishingIdeal k Z) :
    MvPolynomial.eval (curvePoint c 0) g = 0 := by
  have := curvePoint_zero_mem_zeroLocus_vanishingIdeal c Z hZ
  rw [MvPolynomial.mem_zeroLocus_iff] at this
  have h := this g hg
  rwa [MvPolynomial.aeval_eq_eval] at h

/-- **L6.0 for a Zariski-closed target.** If `Z = zeroLocus (vanishingIdeal Z)` (Zariski-closed)
and the curve lands in `Z` away from `0`, the limit point itself lies in `Z` — not just the
closure. -/
theorem curvePoint_zero_mem_of_isZariskiClosed [Infinite k]
    (c : σ → Polynomial k) (Z : Set (σ → k))
    (hZclosed : Z = zeroLocus k (vanishingIdeal k Z))
    (hZ : ∀ t : k, t ≠ 0 → curvePoint c t ∈ Z) :
    curvePoint c 0 ∈ Z := by
  rw [hZclosed]
  exact curvePoint_zero_mem_zeroLocus_vanishingIdeal c Z hZ

/-! ## Non-vacuity witness -/

/-- The constant curve `t ↦ a` has limit point `a` (`curvePoint (C ∘ a) 0 = a`): the simplest
curve. -/
theorem curvePoint_const_zero (a : σ → k) :
    curvePoint (fun x ↦ Polynomial.C (a x)) 0 = a := by
  funext x; simp

/-- Non-vacuity witness for L6.0: the constant curve at a point `a ∈ Z`. It lands in `Z` for every
`t` (so in particular for `t ≠ 0`), and its limit `a` lies in `zeroLocus (vanishingIdeal Z)` — a
concrete satisfiable instance of the conclusion (`a` is in the closure of any set containing it). -/
example [Infinite k] (Z : Set (σ → k)) (a : σ → k) (ha : a ∈ Z) :
    a ∈ zeroLocus k (vanishingIdeal k Z) := by
  have hmem : ∀ t : k, t ≠ 0 → curvePoint (fun x ↦ Polynomial.C (a x)) t ∈ Z := by
    intro t _
    rw [show curvePoint (fun x ↦ Polynomial.C (a x)) t = a by funext x; simp]
    exact ha
  have h := curvePoint_zero_mem_zeroLocus_vanishingIdeal (fun x ↦ Polynomial.C (a x)) Z hmem
  rwa [curvePoint_const_zero] at h

end DLNFibre.Core
