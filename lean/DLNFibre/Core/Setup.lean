import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# `DLNFibre.Core.Setup` — ambient objects of the quiver engine

The network-free substrate for the geometry of the DLN fibre (Le Halleur–Rimányi 2024, §2): for
a fixed dimension vector `d = (d₀, …, d_N)` over a `CommRing k`, the space `Rep_d` of composable
matrix tuples, the multiplication map `mult : (A₁,…,A_N) ↦ A_N ⋯ A₁`, the product-rank loci `Σ^r`
/ `Σ^{≤r}`, and the fibre `mult⁻¹(B)`.

**Encoding.** The dimension vector is a fixed parameter `d : Fin (N + 1) → ℕ`, and `Rep_d` is the
product space `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k` (`Aᵢ` maps
`Fin (d_{i-1}) → Fin (d_i)`). This matches the paper's `Rep_d = ∏ Mat_{dᵢ,d_{i-1}}` directly, so
the rank loci and fibres are honest `Set (Tuple d)` for a *fixed* `d`. The ordered product is
defined through the prefix products `multPrefix`, whose `rfl` step lemmas (`multPrefix_zero`,
`multPrefix_succ`) let downstream lemmas recurse on the product without unfolding `Fin.induction`.

**Typeclass.** `CommRing k` is the weakest class carrying `Matrix.rank` (which is defined over a
`CommRing`); a `Field` is not needed for these definitions. **Dependency rule:** never import
`DLNFibre.DLN`.
-/

namespace DLNFibre.Core

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- `Rep_d`: a composable matrix tuple `(A₁, …, A_N)` for the dimension vector `d`, with
`Aᵢ : Matrix (Fin dᵢ) (Fin d_{i-1}) k`. -/
abbrev Tuple (d : Fin (N + 1) → ℕ) : Type u :=
  ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k

/-- The prefix product `Aⱼ ⋯ A₁ : Matrix (Fin dⱼ) (Fin d₀) k` of the first `j` factors. -/
def multPrefix (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    (j : Fin (N + 1)) → Matrix (Fin (d j)) (Fin (d 0)) k :=
  Fin.induction (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) (fun i prev ↦ A i * prev)

/-- The empty prefix product is the identity. -/
@[simp] theorem multPrefix_zero (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    multPrefix d A 0 = 1 := rfl

/-- The prefix product gains its next factor on the left:
`(prefix to i.succ) = Aᵢ * (prefix to i)`. -/
@[simp] theorem multPrefix_succ (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i : Fin N) :
    multPrefix d A i.succ = A i * multPrefix d A i.castSucc := rfl

/-- The multiplication map `mult (A₁,…,A_N) = A_N ⋯ A₁ : Matrix (Fin d_N) (Fin d₀) k`. -/
def mult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k :=
  multPrefix d A (Fin.last N)

/-- The product-rank-`r` locus `Σ^r = {A | rank (mult A) = r}`. -/
def productRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
  {A | (mult d A).rank = r}

/-- The product-rank-`≤ r` locus `Σ^{≤r} = {A | rank (mult A) ≤ r}` (the union `⋃_{s ≤ r} Σ^s`). -/
def productRankLocusLE (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
  {A | (mult d A).rank ≤ r}

/-- The fibre `mult⁻¹(B) = {A | mult A = B}` over a target matrix `B`. -/
def fibre (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Set (Tuple (k := k) d) :=
  {A | mult d A = B}

/-- `Σ^r` membership is exactly `rank (mult A) = r`. -/
theorem mem_productRankLocus {d : Fin (N + 1) → ℕ} {r : ℕ} {A : Tuple (k := k) d} :
    A ∈ productRankLocus d r ↔ (mult d A).rank = r := Iff.rfl

/-- `Σ^{≤r}` membership is exactly `rank (mult A) ≤ r`. -/
theorem mem_productRankLocusLE {d : Fin (N + 1) → ℕ} {r : ℕ} {A : Tuple (k := k) d} :
    A ∈ productRankLocusLE d r ↔ (mult d A).rank ≤ r := Iff.rfl

/-- Fibre membership is exactly `mult A = B`. -/
theorem mem_fibre {d : Fin (N + 1) → ℕ} {A : Tuple (k := k) d}
    {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k} :
    A ∈ fibre d B ↔ mult d A = B := Iff.rfl

/-- The fibre is the preimage of the singleton `{B}` under `mult`, matching the paper's
`mult⁻¹(B)`. -/
theorem fibre_eq_preimage (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    fibre d B = mult d ⁻¹' {B} := rfl

section Witness

/-! ## Non-vacuity witness

`N = 2`, dimension vector `(2, 2, 2)`, over `ℤ`: with `A₁ = [[1,2],[0,1]]` and `A₂ = [[1,0],[3,1]]`,
`mult = A₂ A₁ = [[1,2],[3,7]]`, so this tuple lies in `Σ^2` and in the fibre over
`[[1,2],[3,7]]`. -/

/-- Witness dimension vector `(2, 2, 2)`. -/
def dWitness : Fin 3 → ℕ := ![2, 2, 2]

/-- Witness tuple `(A₁, A₂)` over `ℤ`. -/
def tupleWitness : Tuple (k := ℤ) dWitness := fun i ↦
  match i with
  | 0 => !![1, 2; 0, 1]
  | 1 => !![1, 0; 3, 1]

/-- `mult` computes the ordered product `A₂ A₁` on the witness. -/
example : mult dWitness tupleWitness = !![1, 2; 3, 7] := by
  unfold mult multPrefix tupleWitness dWitness
  decide

/-- The witness lies in the fibre over its own product — the loci and the fibre are inhabited. -/
example : tupleWitness ∈ fibre dWitness (!![1, 2; 3, 7]) := by
  change mult dWitness tupleWitness = !![1, 2; 3, 7]
  unfold mult multPrefix tupleWitness dWitness
  decide

end Witness

end DLNFibre.Core
