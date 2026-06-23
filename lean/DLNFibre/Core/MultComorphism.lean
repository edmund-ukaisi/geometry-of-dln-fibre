import DLNFibre.Core.Setup
import DLNFibre.Core.OrbitCodim
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.RingTheory.Nullstellensatz

/-!
# `DLNFibre.Core.MultComorphism` — the coordinate-ring map of `mult` and the fibre's ideal (L4.6)

The keystone of the Lehalleur–Rimányi Lemma-4.6 build: the coordinate-ring map for the
multiplication map `mult` and the identification of the fibre `mult⁻¹(B)` as a zero-locus /
coordinate-ring quotient.
Thread 04 found "the engine has no ring map for `mult`"; the unblocking insight is that `mult` is
defined over **any** `CommRing` (`Core.Setup.mult`), so the product-entry polynomials are just
`mult` applied to the **generic** tuple over `MvPolynomial (RepCoord d) k`. It is constructible.

The deliverables, for a fixed dimension vector `d : Fin (N+1) → ℕ`:

1. **`multPoly`** — the generic product entries `(mult d genericTuple) r c`, where
   `genericTuple i a b = MvPolynomial.X ⟨i, a, b⟩` re-uses the existing `mult`/`multPrefix` over the
   polynomial ring (no new recursion).
2. **`eval_multPoly` (the bridge)** — `MvPolynomial.eval (canonicalCoord d A) (multPoly d r c) =
   (mult d A) r c` for every tuple `A`. `eval (canonicalCoord d A)` is a ring hom, so it commutes
   with the matrix product (`Matrix.map_mul`); the single-variable case is `canonicalCoord_apply` /
   `eval_X`. This is the load-bearing lemma; everything else is corollary.
3. **Fibre as zero-locus** — `canonicalCoord d '' (fibre d B) = zeroLocus {multPoly r c − C·B r c}`.
4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
   Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the fibre's vanishing ideal as the
   radical of `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`.
5. **The comorphism + `Ideal.map`** — `multComap d := aeval (fun rc ↦ multPoly d rc.1 rc.2)`, and
   `fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint B)`: the fibre generator-ideal is
   the extension of `B`'s maximal ideal along the comorphism — the "fibre coordinate ring `=
   R_total ⧸ m_B·R_total`" object the height-squeeze (F2) consumes.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-! ## API contracts (durable, pre-staged) -/

section Contracts
variable {σ R : Type*} [CommRing R]

/-- `eval f` is a ring hom; `Matrix.map` of a product is the product of maps. -/
example {m n o : Type*} [Fintype n] (f : σ → R) (L : Matrix m n (MvPolynomial σ R))
    (M : Matrix n o (MvPolynomial σ R)) :
    (L * M).map (eval f) = L.map (eval f) * M.map (eval f) := Matrix.map_mul

/-- `eval f` sends the generator `X i` to its coordinate `f i`. -/
example (f : σ → R) (i : σ) : eval f (X i : MvPolynomial σ R) = f i := eval_X i

/-- `Ideal.map` of a span is the span of the image. -/
example {S : Type*} [CommRing S] (φ : R →+* S) (s : Set R) :
    Ideal.map φ (Ideal.span s) = Ideal.span (φ '' s) := Ideal.map_span φ s

end Contracts

/-! ## The generic product entries `multPoly` -/

/-- The **generic tuple**: each entry is its own coordinate variable,
`(genericTuple i) a b = X ⟨i, a, b⟩`, a tuple over the coordinate polynomial ring. -/
noncomputable def genericTuple (d : Fin (N + 1) → ℕ) :
    Tuple (k := MvPolynomial (RepCoord d) k) d :=
  fun i a b ↦ X ⟨i, a, b⟩

@[simp] theorem genericTuple_apply (d : Fin (N + 1) → ℕ) (i : Fin N)
    (a : Fin (d i.succ)) (b : Fin (d i.castSucc)) :
    (genericTuple (k := k) d i) a b = X ⟨i, a, b⟩ := rfl

/-- **The generic product entries** `multPoly d r c = (mult d genericTuple) r c`: the polynomial in
the coordinate ring `MvPolynomial (RepCoord d) k` giving the `(r,c)` entry of the product. -/
noncomputable def multPoly (d : Fin (N + 1) → ℕ) :
    Fin (d (Fin.last N)) → Fin (d 0) → MvPolynomial (RepCoord d) k :=
  fun r c ↦ (mult d (genericTuple (k := k) d)) r c

/-! ## The bridge: evaluating the generic product gives the actual product -/

/-- `eval (canonicalCoord d A)` carries `genericTuple` to `A`, entrywise: the generic matrix factor
`A i`'s coordinate variables evaluate to the entries of `A i`. -/
theorem map_eval_genericTuple (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i : Fin N) :
    ((genericTuple (k := k) d i)).map (eval (canonicalCoord d A)) = A i := by
  ext a b
  simp [genericTuple, canonicalCoord_apply]

/-- The ring hom `eval (canonicalCoord d A)` carries the generic prefix product to the actual prefix
product, entrywise — the induction spine of the bridge. -/
theorem map_eval_multPrefix (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (j : Fin (N + 1)) :
    (multPrefix d (genericTuple (k := k) d) j).map (eval (canonicalCoord d A))
      = multPrefix d A j := by
  induction j using Fin.induction with
  | zero =>
    simp only [multPrefix_zero]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ i ih =>
    rw [multPrefix_succ, multPrefix_succ, Matrix.map_mul, ih, map_eval_genericTuple]

/-- **The bridge (load-bearing).** Evaluating the generic product entry `multPoly d r c` at the
coordinates of a tuple `A` reproduces the actual product entry `(mult d A) r c`. -/
theorem eval_multPoly (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    eval (canonicalCoord d A) (multPoly d r c) = (mult d A) r c := by
  have h := map_eval_multPrefix d A (Fin.last N)
  have := congrFun (congrFun (congrArg (fun M ↦ M) h) r) c
  simpa [multPoly, mult, Matrix.map_apply] using this

/-! ## The fibre as a zero-locus and its vanishing ideal (over a field) -/

section Field

variable {k : Type u} [Field k] {N : ℕ}

/-- The generating set of the fibre over `B`: the polynomials `multPoly d r c − C (B r c)`, one per
target entry; their common zero-locus is the fibre. -/
noncomputable def fibreGenSet (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Set (MvPolynomial (RepCoord d) k) :=
  Set.range (fun rc : Fin (d (Fin.last N)) × Fin (d 0) ↦ multPoly d rc.1 rc.2 - C (B rc.1 rc.2))

/-- A point `x` lies in the zero-locus of `fibreGenSet d B` iff `eval x (multPoly d r c) = B r c`
for every `(r, c)`. -/
theorem mem_zeroLocus_fibreGenSet (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (x : RepCoord d → k) :
    x ∈ zeroLocus k (Ideal.span (fibreGenSet d B)) ↔
      ∀ r c, eval x (multPoly d r c) = B r c := by
  rw [zeroLocus_span]
  constructor
  · intro h r c
    have := h _ ⟨(r, c), rfl⟩
    rw [aeval_eq_eval] at this
    simpa [sub_eq_zero] using this
  · rintro h p ⟨⟨r, c⟩, rfl⟩
    rw [aeval_eq_eval]
    simp [h r c]

/-- **Fibre as a zero-locus.** The image of the fibre `mult⁻¹(B)` under the canonical flattening is
exactly the common zero-locus of `{multPoly d r c − C (B r c)}`. Membership chase via
`eval_multPoly` and `Matrix.ext_iff`. -/
theorem image_fibre_eq_zeroLocus (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    canonicalCoord d '' (fibre d B) = zeroLocus k (Ideal.span (fibreGenSet d B)) := by
  ext x
  rw [mem_zeroLocus_fibreGenSet]
  constructor
  · rintro ⟨A, hA, rfl⟩ r c
    rw [eval_multPoly]
    exact congrFun (congrFun (mem_fibre.mp hA) r) c
  · intro hx
    refine ⟨(canonicalCoord d).symm x, ?_, (canonicalCoord d).apply_symm_apply x⟩
    rw [mem_fibre]
    ext r c
    have := hx r c
    rw [← (canonicalCoord d).apply_symm_apply x, eval_multPoly] at this
    exact this

/-- The **fibre generator ideal** `span {multPoly d r c − C (B r c)}` — the ideal cutting out the
fibre. -/
noncomputable def fibreGenIdeal (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Ideal (MvPolynomial (RepCoord d) k) :=
  Ideal.span (fibreGenSet d B)

/-- **The fibre's vanishing ideal is the radical of the generator ideal.** Over an algebraically
closed field, the engine's strong Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the
vanishing ideal of the fibre's image as the radical of `fibreGenIdeal d B`. -/
theorem vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
  rw [image_fibre_eq_zeroLocus, fibreGenIdeal,
    vanishingIdeal_zeroLocus_eq_radical (K := k)]

/-! ## The comorphism and the `Ideal.map` identification -/

/-- The **comorphism** of `mult`: the `k`-algebra map of coordinate rings
`MvPolynomial (Fin d_N × Fin d_0) k →ₐ[k] MvPolynomial (RepCoord d) k` sending the target entry
variable `X (r,c)` to the generic product entry `multPoly d r c`. -/
noncomputable def multComap (d : Fin (N + 1) → ℕ) :
    MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k →ₐ[k] MvPolynomial (RepCoord d) k :=
  aeval (fun rc ↦ multPoly d rc.1 rc.2)

@[simp] theorem multComap_X (d : Fin (N + 1) → ℕ) (rc : Fin (d (Fin.last N)) × Fin (d 0)) :
    multComap d (X rc : MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k)
      = multPoly d rc.1 rc.2 := by
  simp [multComap]

/-- The **maximal ideal of the point `B`** in the target coordinate ring:
`span {X (r,c) − C (B r c)}`, the vanishing ideal of the single point `B`. -/
noncomputable def maxIdealOfPoint (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Ideal (MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k) :=
  Ideal.span (Set.range (fun rc : Fin (d (Fin.last N)) × Fin (d 0) ↦ X rc - C (B rc.1 rc.2)))

/-- **The fibre generator ideal is the extension of `B`'s maximal ideal along the comorphism.**
`fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint d B)`: the fibre coordinate ring is
`R_total ⧸ m_B · R_total`, the object the height-squeeze (F2) consumes. -/
theorem fibreGenIdeal_eq_map_maxIdealOfPoint (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    fibreGenIdeal d B = Ideal.map (multComap d).toRingHom (maxIdealOfPoint d B) := by
  rw [maxIdealOfPoint, Ideal.map_span, fibreGenIdeal, fibreGenSet]
  congr 1
  ext p
  constructor
  · rintro ⟨rc, rfl⟩
    exact ⟨X rc - C (B rc.1 rc.2), ⟨rc, rfl⟩, by simp [multComap]⟩
  · rintro ⟨q, ⟨rc, rfl⟩, rfl⟩
    exact ⟨rc, by simp [multComap]⟩

end Field

/-! ## Non-vacuity witness -/

section Witness

/-- The generic product entry `multPoly` at the `(2,2,2)` witness, evaluated at the witness tuple's
coordinates, reproduces the actual product `!![1,2;3,7]` — `eval_multPoly` is non-vacuous. -/
example (r : Fin (dWitness (Fin.last 2))) (c : Fin (dWitness 0)) :
    eval (canonicalCoord dWitness tupleWitness) (multPoly dWitness r c)
      = (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ) r c := by
  rw [eval_multPoly]
  have : mult dWitness tupleWitness = !![1, 2; 3, 7] := by
    unfold mult multPrefix tupleWitness dWitness
    decide
  rw [this]

end Witness

end DLNFibre.Core
