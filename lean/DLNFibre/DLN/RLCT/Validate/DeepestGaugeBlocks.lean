import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks` — gauge-slice → Schur block algebra (#44c sub-1)

The **route-independent** matrix-algebra core of `deepest_gauge_chart_exists` (sub-lemma 1,
controller 2026-06-22). Banks regardless of the L2 transport wrapper (squeeze vs chart): the
geometric content that `deepest_gauge_chart_exists` produces and any transport consumes.

## The obligation (g150/g153 cert, refined)

At a rank-`r`-exact deepest point, each layer gauge-slices to `C_s = [[I+X_s, Y_s],[Z_s, T_s]]`. The
loss is `‖∏C_s − D‖²` with `D = blockdiag[I, 0]` (the deepest product value). Block-summing the
Frobenius norm: `loss = ∑(E²) + ‖P11‖²`, `E` = the regular residuals on the `(0,0),(0,1),(1,0)`
blocks, `P11` = the `(1,1)` block of `∏C`.

**The raw-`∏T` core is INSUFFICIENT** (g153, Codex CE verified): `C1C2C3 = blockdiag[1, −ε⁴]` has
`∑E²=0`, raw `∏T = 0` (interior `T2=0`), but `P11 = −ε⁴` — so `‖P11‖² = ε⁸ ≠ 0 = ‖∏T‖²`. A zero
INTERIOR reduced block produces a nonzero `P11` via gauge interactions invisible to `E`. So the
reduced core MUST be the **Schur complement** `R = P11 − P10·Ainv·P01` (`A = P00 ≈ I` near `w0`),
the gauge-normalized chain — NOT the raw `∏T`.

## The reusable bedrock (from `GeneralR1Recursion`)

The abstract squeeze is already PROVEN there and reused here:
- `hardPivot_schur_blockId` — `L·(fromBlocks 1 b c D)·R = fromBlocks 1 0 0 (D−c·b)` (transvection).
- `schur_row_decomp` — `b·β + D·Γ = b·(1·β + a·Γ) + (D − b·a)·Γ` (the row decomposition).
- `schur_lossDiff_eq_cofactor` — `∑(bErow+SΓ)² − ∑(SΓ)² = ∑ bErow·(bErow+2SΓ)` (loss-diff ∈ ideal).
- `schur_node_squeeze_unif` — the two-sided squeeze, explicit `c₁ = (2(1+T²))⁻¹`, `c₂ = 2+2T²`.

The genuine #44c work here is the **L2 geometric presentation**: the 2-factor gauge-sliced product
in Schur block form, matched to the `schur_*` shape (`Erow` = regular residual row, `b` = pivot
column `→ 0` at `w0`, `S·Γ` = the reduced chain).

## Status

ROUTE-INDEPENDENT bedrock (sub-1): the 2-factor block product + the Schur `(1,1)` split, GREEN. The
`L`-fold + the gauge-slice presentation are the next layers; the wrapper is controller-wired.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The 2-factor block product** (`g150_gauge_chart` cert). For two gauge-sliced rank-`r` layers
`C₁ = fromBlocks (I+X₁) Y₁ Z₁ T₁`, `C₂ = fromBlocks (I+X₂) Y₂ Z₂ T₂`, the product `C₁·C₂` has blocks
`(0,0) = (I+X₁)(I+X₂)+Y₁Z₂`, `(0,1) = (I+X₁)Y₂+Y₁T₂`, `(1,0) = Z₁(I+X₂)+T₁Z₂`, `(1,1) = Z₁Y₂+T₁T₂`.
Pure `CommRing` block algebra (`fromBlocks_multiply`). -/
theorem twofactor_block_product {r m₁ m₂ m₃ : Type*} [Fintype r] [DecidableEq r]
    [Fintype m₂] {R : Type*} [CommRing R]
    (X₁ : Matrix r r R) (Y₁ : Matrix r m₂ R) (Z₁ : Matrix m₁ r R) (T₁ : Matrix m₁ m₂ R)
    (X₂ : Matrix r r R) (Y₂ : Matrix r m₃ R) (Z₂ : Matrix m₂ r R) (T₂ : Matrix m₂ m₃ R) :
    (Matrix.fromBlocks (1 + X₁) Y₁ Z₁ T₁) * (Matrix.fromBlocks (1 + X₂) Y₂ Z₂ T₂)
      = Matrix.fromBlocks
          ((1 + X₁) * (1 + X₂) + Y₁ * Z₂) ((1 + X₁) * Y₂ + Y₁ * T₂)
          (Z₁ * (1 + X₂) + T₁ * Z₂) (Z₁ * Y₂ + T₁ * T₂) := by
  rw [Matrix.fromBlocks_multiply]

/-- **The Schur split of the 2-factor product's `(1,1)` block** (g150-fix / g153). The lower-right
Schur complement `R := P₁₁ − P₁₀·Ainv·P₀₁` (`Ainv` = the pivot inverse) is the clean reduced core
(the gauge-normalized chain); `P₁₁ = R + P₁₀·Ainv·P₀₁` exhibits the endpoint leak `P₁₁ − R` as a
product of the regular residuals `P₁₀, P₀₁` (`∈ ideal(reg)`). Pure ring algebra. -/
theorem schur_P11_decomp {r mlo nhi : Type*} [Fintype r] {R : Type*} [Ring R]
    (Ainv : Matrix r r R) (P01 : Matrix r nhi R) (P10 : Matrix mlo r R)
    (P11 : Matrix mlo nhi R) :
    P11 = (P11 - P10 * Ainv * P01) + P10 * Ainv * P01 := by
  rw [sub_add_cancel]

/-- **The Frobenius block-sum** (route-independent). The entrywise-summed `f`-weight of a
`fromBlocks` matrix splits into the four block sums (`f = (·²)` gives the squared-Frobenius split).
The block-summing of `dlnLoss = ∑ f((prod − B)ᵢⱼ)` once the gauge-sliced product is in block form:
`loss = ∑E² + ‖P11‖²`, `E` the regular-residual blocks `(0,0),(0,1),(1,0)`, `P11` the `(1,1)` block.
Pure `Fintype.sum_sum_type`; stated for a general entry weight `f` to dodge a typeclass. -/
theorem frobenius_fromBlocks {r mlo nhi₀ nhi₁ : Type*} [Fintype r] [Fintype mlo]
    [Fintype nhi₀] [Fintype nhi₁] {R S : Type*} [AddCommMonoid S] (f : R → S)
    (E00 : Matrix r nhi₀ R) (E01 : Matrix r nhi₁ R)
    (E10 : Matrix mlo nhi₀ R) (E11 : Matrix mlo nhi₁ R) :
    (∑ i, ∑ j, f (Matrix.fromBlocks E00 E01 E10 E11 i j))
      = ((∑ i, ∑ j, f (E00 i j)) + (∑ i, ∑ j, f (E01 i j)))
        + ((∑ i, ∑ j, f (E10 i j)) + (∑ i, ∑ j, f (E11 i j))) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
    rw [Finset.sum_add_distrib]
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    rw [Finset.sum_add_distrib]

/-- **The matrix-core comparability squeeze** (#54, the load-bearing #44c obligation, route- and
encoding-independent). With the loss-block decomposed as `P₁₁ = leak + R` entrywise (`hsplit`: `R` =
the gauge-normalized Schur core, `leak` = the regular×regular endpoint leak) and the leak charged to
the regular block `∑ leak² ≤ t²·∑ E²` (`hleak`; `t = ‖pivot‖ → 0` at `w0`), the loss `∑E² + ‖P₁₁‖²`
is two-sidedly comparable to the clean form `∑E² + ‖R‖²`:
`(2(1+t²))⁻¹·(∑E²+‖R‖²) ≤ ∑E²+‖P₁₁‖² ≤ (2+2t²)·(∑E²+‖R‖²)`.
The thin specialisation of `squeeze_bounds_abstract` (`p = leak`, `s = R`, `p+s = P₁₁`). The g153
raw-`∏T` refutation is dodged: the leak is in the regular ideal (`hleak`), so its excess is charged
to `∑E²`, not the core — exactly where the raw-`∏T` core was insufficient. -/
theorem core_comparability_squeeze {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → ℝ) (P11 leak Rcore : κ → ℝ) (t : ℝ)
    (hsplit : ∀ j, P11 j = leak j + Rcore j)
    (hleak : (∑ j, (leak j) ^ 2) ≤ t ^ 2 * (∑ i, (E i) ^ 2)) :
    ((∑ i, (E i) ^ 2) + (∑ j, (Rcore j) ^ 2))
        ≤ (2 * (1 + t ^ 2)) * ((∑ i, (E i) ^ 2) + (∑ j, (P11 j) ^ 2))
    ∧ ((∑ i, (E i) ^ 2) + (∑ j, (P11 j) ^ 2))
        ≤ (2 + 2 * t ^ 2) * ((∑ i, (E i) ^ 2) + (∑ j, (Rcore j) ^ 2)) := by
  simp only [hsplit]
  exact squeeze_bounds_abstract E leak Rcore t hleak

/-- **The full-product Frobenius core split** (route-independent, g156-confirmed). For the FULL chain
product written in block form `P = fromBlocks P00 P01 P10 P11` with the pivot `P00` invertible, the
squared-Frobenius loss against the deepest value `blockdiag[1, 0]` splits as the regular-residual sum
`∑E²` (over the `(0,0)−1`, `(0,1)`, `(1,0)` blocks) plus `‖P11‖²`, and `P11 = leak + R` with the
**full-product Schur complement** `R = P11 − P10·⅟P00·P01` and `leak = P10·⅟P00·P01` (the regular
endpoint leak `∈ ideal(P10, P01)`). The honest reduced core is `R` (g156: NOT `∏S_s` — the Schur
complement of a product is not the product of Schur complements; but `R − ∏S_s ∈ ideal(E)`, so the
two squeeze the same). The thin assembly of `frobenius_fromBlocks` (`f = ·²`) + `schur_P11_decomp`,
ready for `core_comparability_squeeze`. -/
theorem fullProduct_core_split {r mlo nhi : Type*} [Fintype r] [DecidableEq r] [Fintype mlo]
    [Fintype nhi]
    (P00 : Matrix r r ℝ) (P01 : Matrix r nhi ℝ) (P10 : Matrix mlo r ℝ) (P11 : Matrix mlo nhi ℝ)
    [Invertible P00] :
    (∑ i, ∑ j, ((Matrix.fromBlocks P00 P01 P10 P11
            - Matrix.fromBlocks (1 : Matrix r r ℝ) (0 : Matrix r nhi ℝ)
                (0 : Matrix mlo r ℝ) (0 : Matrix mlo nhi ℝ)) i j) ^ 2)
        = (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
            + ((∑ i, ∑ j, (P10 i j) ^ 2) + (∑ i, ∑ j, (P11 i j) ^ 2)))
      ∧ (∀ i j, P11 i j = (P10 * ⅟P00 * P01) i j + (P11 - P10 * ⅟P00 * P01) i j) := by
  refine ⟨?_, ?_⟩
  · -- Frobenius block split: `fromBlocks − blockdiag[1,0] = fromBlocks (P00−1) P01 P10 P11`.
    have hsub : (Matrix.fromBlocks P00 P01 P10 P11
          - Matrix.fromBlocks (1 : Matrix r r ℝ) (0 : Matrix r nhi ℝ)
              (0 : Matrix mlo r ℝ) (0 : Matrix mlo nhi ℝ))
        = Matrix.fromBlocks (P00 - 1) P01 P10 P11 := by
      rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
      simp [sub_eq_add_neg]
    rw [hsub]
    exact frobenius_fromBlocks (fun x => x ^ 2) (P00 - 1) P01 P10 P11
  · intro i j
    have hd := schur_P11_decomp (⅟P00) P01 P10 P11
    rw [hd]
    simp [Matrix.add_apply]

/-- **Frobenius submultiplicativity** (2-factor, entrywise squared). The squared-Frobenius energy of a
matrix product is bounded by the product of the factor energies: per-entry Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) on `(M·N) i j = ∑ₖ M i k · N k j`, then the double-sum factors by
`Finset.sum_mul_sum`. Route-independent bedrock for the leak bound `hleak`. -/
theorem frobenius_mul_le {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (M : Matrix a b ℝ) (N : Matrix b c ℝ) :
    (∑ i, ∑ j, ((M * N) i j) ^ 2)
      ≤ (∑ i, ∑ k, (M i k) ^ 2) * (∑ j, ∑ k, (N k j) ^ 2) := by
  have hentry : ∀ i j, ((M * N) i j) ^ 2 ≤ (∑ k, (M i k) ^ 2) * (∑ k, (N k j) ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => M i k) (fun k => N k j)
  calc (∑ i, ∑ j, ((M * N) i j) ^ 2)
      ≤ ∑ i, ∑ j, (∑ k, (M i k) ^ 2) * (∑ k, (N k j) ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (∑ i, ∑ k, (M i k) ^ 2) * (∑ j, ∑ k, (N k j) ^ 2) :=
        (Finset.sum_mul_sum Finset.univ Finset.univ
          (fun i => ∑ k, (M i k) ^ 2) (fun j => ∑ k, (N k j) ^ 2)).symm

/-- **The leak bound** (`hleak` discharge, route-independent). The endpoint leak `leak = P10·N·P01`
(`N = ⅟P00 ≈ I` near the deepest point) has squared-Frobenius energy bounded by
`‖N·P01‖²·(∑ P10²)`, hence (since both `P10, P01` sit inside the regular residual energy `E`, and one
of them is `≤ t²` near `w0`) is charged to `t²·∑E²` via `core_comparability_squeeze`. Here stated as
the clean two-factor chain `∑ leak² ≤ (∑ P10²)·(∑ (N·P01)²)` — the geometric `t²` smallness is
supplied by the consumer from `P10(w0)=0` + continuity. -/
theorem leak_frobenius_bound {r mlo nhi : Type*} [Fintype r] [Fintype mlo] [Fintype nhi]
    (N : Matrix r r ℝ) (P01 : Matrix r nhi ℝ) (P10 : Matrix mlo r ℝ) :
    (∑ i, ∑ j, ((P10 * N * P01) i j) ^ 2)
      ≤ (∑ i, ∑ k, (P10 i k) ^ 2) * (∑ j, ∑ k, ((N * P01) k j) ^ 2) := by
  rw [Matrix.mul_assoc]
  exact frobenius_mul_le P10 (N * P01)

/-- **The triple-product Frobenius upper bound**: `∑(P·A·Q)² ≤ (∑P²)·(∑(A·Q)²)` (one `frobenius_mul_le`
on `P·(A·Q)`), used both directions for the conjugation comparability. -/
theorem frobenius_triple_le {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (P : Matrix a b ℝ) (A : Matrix b c ℝ) (Q : Matrix c d ℝ) :
    (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
      ≤ (∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, ((A * Q) k j) ^ 2) := by
  rw [Matrix.mul_assoc]; exact frobenius_mul_le P (A * Q)

/-- The transposed-order Frobenius product bound: `∑ j, ∑ k, ((M·N) k j)² ≤ (∑M²)·(∑N²)` (the outer
sum over the RIGHT-matrix columns), via `Finset.sum_comm` on `frobenius_mul_le`. -/
theorem frobenius_mul_le' {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (M : Matrix a b ℝ) (N : Matrix b c ℝ) :
    (∑ j, ∑ k, ((M * N) k j) ^ 2)
      ≤ (∑ i, ∑ k, (M i k) ^ 2) * (∑ j, ∑ k, (N k j) ^ 2) := by
  have hcomm : (∑ j, ∑ k, ((M * N) k j) ^ 2) = ∑ i, ∑ j, ((M * N) i j) ^ 2 := Finset.sum_comm
  rw [hcomm]; exact frobenius_mul_le M N

/-- **Conjugation Frobenius comparability** (route-independent, the #80 STEP-1 endpoint-frame bound).
For FIXED invertible endpoint frames `P, Q` (the deepest gauge frame's two boundary units, #77/(iii)),
the squared-Frobenius energy of the conjugate `P·A·Q` is two-sidedly bounded by that of `A`:
`∑A² ≤ (∑Pi²·∑Qi²)·∑(P·A·Q)²` and `∑(P·A·Q)² ≤ (∑P²·∑Q²)·∑A²` (`Pi, Qi` the inverses). The upper bound
is `frobenius_triple_le`; the lower transports it through `A = Pi·(P·A·Q)·Qi`. The bounded conjugation
carrying `dlnLoss = ‖∏A − B‖² = ‖Pi·(∏C − D)·Qi‖²` to the comparable `‖∏C − D‖²` (the framed loss) —
the interior frames telescope (`G_s = I`, #77 (iii)), leaving only the constant endpoint conjugation. -/
theorem conjugation_frobenius_comparable {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (P : Matrix n n ℝ) (Q : Matrix m m ℝ) (Pi : Matrix n n ℝ) (Qi : Matrix m m ℝ)
    (hP : Pi * P = 1) (hQ : Q * Qi = 1) (A : Matrix n m ℝ) :
    (∑ i, ∑ j, (A i j) ^ 2)
        ≤ ((∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2))
            * (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
    ∧ (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
        ≤ ((∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, (Q k j) ^ 2)) * (∑ i, ∑ j, (A i j) ^ 2) := by
  have hnnP : (0 : ℝ) ≤ ∑ i, ∑ k, (P i k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnnPi : (0 : ℝ) ≤ ∑ i, ∑ k, (Pi i k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · -- lower: `A = Pi·(P·A·Q)·Qi`, then `frobenius_triple_le` + `frobenius_mul_le'` on the `Qi`-factor.
    have hA : A = Pi * (P * A * Q) * Qi := by
      have : Pi * (P * A * Q) * Qi = (Pi * P) * A * (Q * Qi) := by
        simp only [Matrix.mul_assoc]
      rw [this, hP, hQ, Matrix.one_mul, Matrix.mul_one]
    calc (∑ i, ∑ j, (A i j) ^ 2)
        = ∑ i, ∑ j, ((Pi * (P * A * Q) * Qi) i j) ^ 2 := by rw [← hA]
      _ ≤ (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, ((P * A * Q) * Qi) k j ^ 2) :=
          frobenius_triple_le Pi (P * A * Q) Qi
      _ ≤ (∑ i, ∑ k, (Pi i k) ^ 2) * ((∑ i, ∑ k, ((P * A * Q) i k) ^ 2)
            * (∑ j, ∑ k, (Qi k j) ^ 2)) :=
          mul_le_mul_of_nonneg_left (frobenius_mul_le' (P * A * Q) Qi) hnnPi
      _ = (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2)
            * (∑ i, ∑ j, ((P * A * Q) i j) ^ 2) := by ring
  · -- upper: `frobenius_triple_le P A Q`, then `frobenius_mul_le'` on the `A·Q`-factor.
    calc (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
        ≤ (∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, ((A * Q) k j) ^ 2) := frobenius_triple_le P A Q
      _ ≤ (∑ i, ∑ k, (P i k) ^ 2) * ((∑ i, ∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (Q k j) ^ 2)) :=
          mul_le_mul_of_nonneg_left (frobenius_mul_le' A Q) hnnP
      _ = (∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, (Q k j) ^ 2) * (∑ i, ∑ j, (A i j) ^ 2) := by ring

/-- **The full-product loss squeeze** (route-independent, the #80 matrix-core). For the FULL chain
product `P = fromBlocks P00 P01 P10 P11` with pivot `P00` invertible (`= I` near the deepest), the
squared-Frobenius loss against `D = blockdiag[1,0]` is two-sidedly comparable to `∑E² + ‖R‖²`, where
`∑E²` is the regular-residual energy (`(P00−1)`, `P01`, `P10` blocks) and `R = P11 − P10·⅟P00·P01` is
the full-product Schur core. The leak `P11 − R = P10·⅟P00·P01` is charged to `∑E²` (`hleak`: its
energy `≤ t²·∑E²`, supplied by the consumer from `P10, P01 → 0` + bounded `⅟P00` near the deepest).
Assembles `fullProduct_core_split` (the `∑E²+‖P11‖²` decomposition + `P11 = leak + R`) into
`core_comparability_squeeze`. The genuine `c₁ < c₂` squeeze (NOT exact) the loss-side needs. -/
theorem fullProduct_loss_squeeze {r mlo nhi : Type*} [Fintype r] [DecidableEq r] [Fintype mlo]
    [Fintype nhi]
    (P00 : Matrix r r ℝ) (P01 : Matrix r nhi ℝ) (P10 : Matrix mlo r ℝ) (P11 : Matrix mlo nhi ℝ)
    [Invertible P00] (t : ℝ)
    (hleak : (∑ i, ∑ j, ((P10 * ⅟P00 * P01) i j) ^ 2)
        ≤ t ^ 2 * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
            + (∑ i, ∑ j, (P10 i j) ^ 2))) :
    (((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2)) + (∑ i, ∑ j, (P10 i j) ^ 2))
          + (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2)))
        ≤ (2 * (1 + t ^ 2)) * (∑ i, ∑ j, ((Matrix.fromBlocks P00 P01 P10 P11
            - Matrix.fromBlocks (1 : Matrix r r ℝ) (0 : Matrix r nhi ℝ)
                (0 : Matrix mlo r ℝ) (0 : Matrix mlo nhi ℝ)) i j) ^ 2)
    ∧ (∑ i, ∑ j, ((Matrix.fromBlocks P00 P01 P10 P11
            - Matrix.fromBlocks (1 : Matrix r r ℝ) (0 : Matrix r nhi ℝ)
                (0 : Matrix mlo r ℝ) (0 : Matrix mlo nhi ℝ)) i j) ^ 2)
        ≤ (2 + 2 * t ^ 2)
            * ((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2)) + (∑ i, ∑ j, (P10 i j) ^ 2))
              + (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2)) := by
  obtain ⟨hfrob, hsplit⟩ := fullProduct_core_split P00 P01 P10 P11
  -- The ⊕-flattened regular-residual energy: `∑_{e:ι} (E e)² = ∑(P00−1)² + (∑P01² + ∑P10²)`.
  have hEflat : (∑ e : (r × r) ⊕ (r × nhi) ⊕ (mlo × r),
        (match e with
          | Sum.inl (i, j) => (P00 - 1) i j
          | Sum.inr (Sum.inl (i, j)) => P01 i j
          | Sum.inr (Sum.inr (i, j)) => P10 i j) ^ 2)
      = ((∑ i, ∑ j, ((P00 - 1) i j) ^ 2)
          + ((∑ i, ∑ j, (P01 i j) ^ 2) + (∑ i, ∑ j, (P10 i j) ^ 2))) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · simp_rw [Fintype.sum_prod_type]
    · rw [Fintype.sum_sum_type]; congr 1 <;> simp_rw [Fintype.sum_prod_type]
  -- The product-index flattenings for `P11`, `leak`, `Rcore`.
  have hP11flat : (∑ p : mlo × nhi, (P11 p.1 p.2) ^ 2) = ∑ i, ∑ j, (P11 i j) ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hleakflat : (∑ p : mlo × nhi, ((P10 * ⅟P00 * P01) p.1 p.2) ^ 2)
      = ∑ i, ∑ j, ((P10 * ⅟P00 * P01) i j) ^ 2 := by rw [Fintype.sum_prod_type]
  have hRflat : (∑ p : mlo × nhi, ((P11 - P10 * ⅟P00 * P01) p.1 p.2) ^ 2)
      = ∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2 := by rw [Fintype.sum_prod_type]
  -- The loss = `∑E² + ∑P11²` (`hfrob`, reassociated to the ⊕-flatten shape).
  have hloss : (∑ i, ∑ j, ((Matrix.fromBlocks P00 P01 P10 P11
        - Matrix.fromBlocks (1 : Matrix r r ℝ) (0 : Matrix r nhi ℝ)
            (0 : Matrix mlo r ℝ) (0 : Matrix mlo nhi ℝ)) i j) ^ 2)
      = ((∑ i, ∑ j, ((P00 - 1) i j) ^ 2)
          + ((∑ i, ∑ j, (P01 i j) ^ 2) + (∑ i, ∑ j, (P10 i j) ^ 2)))
        + (∑ i, ∑ j, (P11 i j) ^ 2) := by
    rw [hfrob]; ring
  -- Apply `core_comparability_squeeze` (single-index) on the flattened blocks.
  have hcc := core_comparability_squeeze
    (ι := (r × r) ⊕ (r × nhi) ⊕ (mlo × r)) (κ := mlo × nhi)
    (E := fun e => match e with
      | Sum.inl (i, j) => (P00 - 1) i j
      | Sum.inr (Sum.inl (i, j)) => P01 i j
      | Sum.inr (Sum.inr (i, j)) => P10 i j)
    (P11 := fun p => P11 p.1 p.2) (leak := fun p => (P10 * ⅟P00 * P01) p.1 p.2)
    (Rcore := fun p => (P11 - P10 * ⅟P00 * P01) p.1 p.2) (t := t)
    (fun p => by simpa using hsplit p.1 p.2)
    (by rw [hleakflat, hEflat]; convert hleak using 2; ring)
  obtain ⟨hcc_le, hcc_ge⟩ := hcc
  rw [hEflat, hP11flat, hRflat] at hcc_le hcc_ge
  constructor
  · -- `(∑E² + ∑R²) ≤ 2(1+t²)·loss`. Reassociate `∑E²` and rw `loss`.
    rw [hloss]; convert hcc_le using 2 <;> ring
  · rw [hloss]; convert hcc_ge using 2 <;> ring

/-- **The per-layer Schur block-diagonalisation** (#44c, g156 / #61 — the corrected `coreAbsorb`
core object). A gauge layer `C = fromBlocks (1+X) Y Z T` with invertible `(0,0)` corner
block-diagonalises by the unipotent transvections `L = [[1,0],[−Z⅟(1+X),1]]`,
`R = [[1,−⅟(1+X)Y],[0,1]]` to `blockdiag[(1+X), S]`, where `S = T − Z·⅟(1+X)·Y` is the **per-layer
Schur complement** — the honest reduced block (#61 CORRECTION: NOT the multiplicative unit
`T·(I−VY)⁻¹`, which is `0` whenever `T=0`; the additive Schur `S` is nonzero when `T=0` but `Z,Y≠0`,
the g153 case). The general-pivot analog of `hardPivot_schur_blockId` (pivot `= 1`). -/
theorem layer_schur_blockDiag {r m : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    {R : Type*} [CommRing R]
    (X : Matrix r r R) (Y : Matrix r m R) (Z : Matrix m r R) (T : Matrix m m R)
    [Invertible (1 + X : Matrix r r R)] :
    Matrix.fromBlocks (1 : Matrix r r R) (0 : Matrix r m R) (-(Z * ⅟(1 + X))) 1
        * Matrix.fromBlocks (1 + X) Y Z T
        * Matrix.fromBlocks (1 : Matrix r r R) (-(⅟(1 + X) * Y)) (0 : Matrix m r R) 1
      = Matrix.fromBlocks (1 + X) (0 : Matrix r m R) (0 : Matrix m r R) (T - Z * ⅟(1 + X) * Y) := by
  have hr1 : (1 + X : Matrix r r R) * ⅟(1 + X) = 1 := mul_invOf_self _
  have hl1 : ⅟(1 + X : Matrix r r R) * (1 + X) = 1 := invOf_mul_self _
  -- Step 1: `L · C = fromBlocks (1+X) Y 0 (T − Z⅟(1+X)·Y)` (clear the lower-left).
  have hLC : Matrix.fromBlocks (1 : Matrix r r R) (0 : Matrix r m R) (-(Z * ⅟(1 + X))) 1
        * Matrix.fromBlocks (1 + X) Y Z T
      = Matrix.fromBlocks (1 + X) Y (0 : Matrix m r R) (T - Z * ⅟(1 + X) * Y) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · -- (1,0): −Z⅟(1+X)·(1+X) + 1·Z = 0
      rw [Matrix.one_mul, Matrix.neg_mul, Matrix.mul_assoc, hl1, Matrix.mul_one, neg_add_cancel]
    · -- (1,1): −Z⅟(1+X)·Y + 1·T = T − Z⅟(1+X)·Y
      rw [Matrix.one_mul, Matrix.neg_mul]; abel
  -- Step 2: `(L·C) · R = fromBlocks (1+X) 0 0 (T − Z⅟(1+X)·Y)` (clear the upper-right).
  rw [hLC, Matrix.fromBlocks_multiply]
  congr 1
  · simp
  · -- (0,1): (1+X)·(−⅟(1+X)·Y) + Y·1 = −(1+X)⅟(1+X)·Y + Y = 0
    rw [Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, hr1, Matrix.one_mul, neg_add_cancel]
  · simp
  · -- (1,1): 0·(−⅟(1+X)·Y) + (T−Z⅟(1+X)·Y)·1 = T − Z⅟(1+X)·Y
    rw [Matrix.zero_mul, Matrix.mul_one, zero_add]

/-- **The core-shear homeomorphism** (the `coreAbsorb` packaging, part (a)). Given a continuous
`shift : Reg × Spec → Core` — the gauge-dependent Schur correction `S_s − T_s = −Z_s(I+X_s)⁻¹Y_s`,
a function of the GAUGE coords (which after `split` live in the regular AND spectator slots, never
the core slot `T` itself) — the self-map `(reg, core, spec) ↦ (reg, core + shift (reg, spec), spec)`
on `Reg × (Core × Spec)` is a homeomorphism fixing the regular and spectator slots, inverse
`core ↦ core − shift (reg, spec)`. The genuine `coreAbsorb` shear (`T_s ↦ S_s = T_s − Z(I+X)⁻¹Y`):
additive in the core slot since the correction does not depend on `T`; `shift` is abstract so the
producer (the gauge slice) supplies the concrete `−Z(I+X)⁻¹Y`. -/
def coreShearHomeo {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] (shift : Reg × Spec → Core) (hshift : Continuous shift) :
    (Reg × (Core × Spec)) ≃ₜ (Reg × (Core × Spec)) where
  toFun := fun q => (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2))
  invFun := fun q => (q.1, (q.2.1 - shift (q.1, q.2.2), q.2.2))
  left_inv := fun q => by simp
  right_inv := fun q => by simp
  continuous_toFun := by
    have hrs : Continuous fun q : Reg × (Core × Spec) => (q.1, q.2.2) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    refine continuous_fst.prodMk (Continuous.prodMk ?_ (continuous_snd.comp continuous_snd))
    exact (continuous_fst.comp continuous_snd).add (hshift.comp hrs)
  continuous_invFun := by
    have hrs : Continuous fun q : Reg × (Core × Spec) => (q.1, q.2.2) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    refine continuous_fst.prodMk (Continuous.prodMk ?_ (continuous_snd.comp continuous_snd))
    exact (continuous_fst.comp continuous_snd).sub (hshift.comp hrs)

/-- `coreShearHomeo` fixes the regular slot. -/
theorem coreShearHomeo_regular {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] (shift : Reg × Spec → Core) (hshift : Continuous shift)
    (q : Reg × (Core × Spec)) : (coreShearHomeo shift hshift q).1 = q.1 := rfl

/-- `coreShearHomeo` fixes the spectator slot. -/
theorem coreShearHomeo_spectator {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] (shift : Reg × Spec → Core) (hshift : Continuous shift)
    (q : Reg × (Core × Spec)) : (coreShearHomeo shift hshift q).2.2 = q.2.2 := rfl

/-- `coreShearHomeo` fixes the origin iff the shift vanishes at the origin gauge coords — the
`coreAbsorb_basepoint` datum (the Schur correction `−Z(I+X)⁻¹Y = 0` at the deepest point, where
`Y = Z = 0`). -/
theorem coreShearHomeo_basepoint {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] [Zero Reg] [Zero Spec]
    (shift : Reg × Spec → Core) (hshift : Continuous shift) (h0 : shift (0, 0) = 0) :
    coreShearHomeo shift hshift (0 : Reg × (Core × Spec)) = 0 := by
  show ((0 : Reg), ((0 : Core) + shift ((0 : Reg), (0 : Spec)), (0 : Spec))) = 0
  rw [h0, add_zero]; rfl

/-! ## The `regAbsorb` packaging — lifting a spec-fixing reg-homeomorphism to `DeepestSplit`

Unlike `coreAbsorb` (an additive shear, GLOBAL det = 1), `regAbsorb` is the NONLINEAR residual map
raw→`E` — a genuine LOCAL diffeo (`det → 0` off `w0`). Its structural shape, abstract over the
concrete `E`: a homeomorphism `Ψ` of the `(Reg × Spec)` part that FIXES the spectator component
(reads reg+spec, writes reg, the spec untouched), lifted to `DeepestSplit = Reg × (Core × Spec)`
fixing the core slot. The concrete `Ψ` (the IFT straightening of `E`) is the producer's; this
packaging is abstract over it. -/

/-- **The reg-slice homeomorphism** (the `regAbsorb` packaging). Given a homeomorphism `Ψ` of
`Reg × Spec` that fixes the spectator component (`(Ψ p).2 = p.2`), the lift
`(reg, core, spec) ↦ ((Ψ (reg, spec)).1, core, spec)` is a self-homeomorphism of `Reg × (Core × Spec)`
fixing the core and spectator slots. The producer supplies `Ψ` = the IFT straightening of the
nonlinear residual `E` (a local diffeo near `w0`, restricted to a homeomorphism on its image). -/
def regSliceHomeo {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2) :
    (Reg × (Core × Spec)) ≃ₜ (Reg × (Core × Spec)) :=
  -- Regroup `Reg × (Core × Spec) ≃ₜ (Reg × Spec) × Core`, act by `Ψ × id` on the `(Reg × Spec)`
  -- factor, regroup back. The `left_inv`/`right_inv`/continuity come free from the component
  -- homeomorphisms; `Ψ` fixing the spectator (`hΨspec`) makes the net action the reg-slice map.
  let reassoc : (Reg × (Core × Spec)) ≃ₜ ((Reg × Spec) × Core) :=
    (Homeomorph.prodCongr (Homeomorph.refl Reg) (Homeomorph.prodComm Core Spec)).trans
      (Homeomorph.prodAssoc Reg Spec Core).symm
  reassoc.trans ((Ψ.prodCongr (Homeomorph.refl Core)).trans reassoc.symm)

/-- `regSliceHomeo` evaluated: `q ↦ ((Ψ (q.1, q.2.2)).1, (q.2.1, (Ψ (q.1, q.2.2)).2))`. The composition
of `prodComm`/`prodAssoc`/`prodCongr` reduces to this by `rfl`. -/
theorem regSliceHomeo_apply {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2)
    (q : Reg × (Core × Spec)) :
    regSliceHomeo Ψ hΨspec q = ((Ψ (q.1, q.2.2)).1, (q.2.1, (Ψ (q.1, q.2.2)).2)) := rfl

/-- `regSliceHomeo` fixes the core slot. -/
theorem regSliceHomeo_core {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2)
    (q : Reg × (Core × Spec)) : (regSliceHomeo Ψ hΨspec q).2.1 = q.2.1 := rfl

/-- `regSliceHomeo` fixes the spectator slot (via `hΨspec`: `Ψ` keeps the spectator component). -/
theorem regSliceHomeo_spectator {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2)
    (q : Reg × (Core × Spec)) : (regSliceHomeo Ψ hΨspec q).2.2 = q.2.2 := by
  rw [regSliceHomeo_apply]; exact hΨspec (q.1, q.2.2)

/-- `regSliceHomeo` fixes the origin iff `Ψ` fixes the origin reg-component — the
`regAbsorb_basepoint` datum (the residual `E = 0` at the deepest point, where all gauge coords `0`). -/
theorem regSliceHomeo_basepoint {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    [Zero Reg] [Zero Core] [Zero Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2)
    (h0 : (Ψ (0, 0)).1 = 0) :
    regSliceHomeo Ψ hΨspec (0 : Reg × (Core × Spec)) = 0 := by
  rw [regSliceHomeo_apply]
  have hsp : (Ψ ((0 : Reg), (0 : Spec))).2 = 0 := hΨspec (0, 0)
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · exact h0
  · exact hsp

/-! ## The E_pivot-INDEPENDENT gauge-block reindex (PIN 2's relabel)

The Frobenius energy `∑ᵢⱼ f(M i j)` of a matrix is invariant under reindexing its rows/columns by
index equivalences (a pure relabel of the double sum). Composed with `fromBlocks_toBlocks` + the
entrywise `frobenius_fromBlocks`, this turns `dlnLoss = ‖prod − B‖²` into its `r ⊕ M`-block-sum form
`∑(P00−blockid)² = ∑P00'² + ∑P01² + ∑P10² + ∑P11²` — the shape `fullProduct_loss_squeeze` consumes.
**This relabel does NOT touch `E_pivot`**: it acts on `dlnLoss`'s OWN already-formed `prod − B`,
independent of the regular-straightening's concrete form (team-lead 2026-06-23: the E_pivot-independent
piece, drivable before the form lands). -/

/-- **Frobenius energy is reindex-invariant** (the relabel of the double sum). For any entry-function
`f`, summing `f` over the entries of a matrix equals summing over the entries of its row/column
reindex `Matrix.reindex e₁ e₂ M` (the index equivs relabel the sum bijectively). -/
theorem frobenius_sum_reindex {a b a' b' : Type*} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    {R S : Type*} [AddCommMonoid S] (f : R → S) (M : Matrix a b R) (e₁ : a ≃ a') (e₂ : b ≃ b') :
    (∑ i, ∑ j, f (Matrix.reindex e₁ e₂ M i j)) = ∑ i, ∑ j, f (M i j) := by
  rw [← Equiv.sum_comp e₁ (fun i => ∑ j, f (Matrix.reindex e₁ e₂ M i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Equiv.sum_comp e₂ (fun j => f (Matrix.reindex e₁ e₂ M (e₁ i) j))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- **The loss as a `r ⊕ M`-block Frobenius sum** (the E_pivot-independent relabel). For any
row/column index equivs `e₁ : a ≃ r ⊕ mlo`, `e₂ : b ≃ r ⊕ nhi`, the square-Frobenius energy
`∑ᵢⱼ (N i j)²` of a matrix `N` equals the four-block sum of `N` reindexed into `r ⊕ _` shape — the
`(P00, P01, P10, P11)` blocks `fullProduct_loss_squeeze` consumes. Pure relabel + `fromBlocks_toBlocks`
+ `frobenius_fromBlocks`; no dependence on the regular straightening. -/
theorem frobenius_sq_eq_blocks {a b r mlo nhi : Type*} [Fintype a] [Fintype b]
    [Fintype r] [Fintype mlo] [Fintype nhi]
    (N : Matrix a b ℝ) (e₁ : a ≃ r ⊕ mlo) (e₂ : b ≃ r ⊕ nhi) :
    (∑ i, ∑ j, (N i j) ^ 2)
      = (((∑ i, ∑ j, ((Matrix.reindex e₁ e₂ N).toBlocks₁₁ i j) ^ 2)
            + (∑ i, ∑ j, ((Matrix.reindex e₁ e₂ N).toBlocks₁₂ i j) ^ 2))
          + ((∑ i, ∑ j, ((Matrix.reindex e₁ e₂ N).toBlocks₂₁ i j) ^ 2)
            + (∑ i, ∑ j, ((Matrix.reindex e₁ e₂ N).toBlocks₂₂ i j) ^ 2))) := by
  rw [← frobenius_sum_reindex (fun x => x ^ 2) N e₁ e₂]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex e₁ e₂ N)]
  rw [frobenius_fromBlocks (fun x => x ^ 2)]

end DLNFibre.DLN.RLCT
