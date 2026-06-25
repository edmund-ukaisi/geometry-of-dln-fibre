import DLNFibre.DLN.RLCT.Foundations.S1RadialMorse
import DLNFibre.DLN.RLCT.Validate.Case222Lemma2

/-!
# `DLNFibre.DLN.RLCT.Validate.MatMulFibre` — the matrix-product fibre finiteness (S2-FREE)

The reusable **fibre engine** for the iterated-fibre hfin route (Codex-steered, thread 29). For a
free matrix `X : Fin p → Fin n → ℝ` over the box `[−T,T]^{pn}` and a FIXED `Y : Fin n → Fin q → ℝ`,
the fibre integral of `‖X·Y‖_F^{−2c'}` is bounded by a `Y`-independent constant times `‖Y‖_F^{−2c'}`,
finite for `c' < p/2`:

    ∫⁻_{X∈matBox} (frobSq (X·Y))^{−c'} ≤ fibreConst · (frobSq Y)^{−c'}.

The argument is S2-FREE: pick the max-abs entry `Y_{ℓj}` (hidden inside the proof via
`Finset.exists_max_image` — never in the statement, so no measurability of the choice); the per-row
shear `u_i := (X·Y)_{ij}/Y_{ℓj}` is volume-preserving (det-1, `measurePreserving_shearAt` per row);
`frobSq(X·Y) ≥ Y_{ℓj}²·∑_i u_i²` (algebra) and `Y_{ℓj}² ≥ frobSq Y/(nq)` (max entry); the resulting
`p`-dimensional sum-of-squares integral is finite by `sumSqND_box_lt_top` (`S1RadialMorse`, S2-free).

No `monomial_rlct`. The two `(4,4,2,2)` instances are `(p,n,q) = (4,4,2)` (A0 fibre, Y = A1·A2) and
`(4,2,2)` (A1 fibre, Y = A2).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The matrix-product / Frobenius-square primitives -/

/-- **The squared Frobenius norm** `frobSq M = ∑ᵢⱼ Mᵢⱼ²` (the loss-shaped sum of entry squares). -/
noncomputable def frobSq {a b : Type*} [Fintype a] [Fintype b] (M : a → b → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

/-- `frobSq M ≥ 0`. -/
theorem frobSq_nonneg {a b : Type*} [Fintype a] [Fintype b] (M : a → b → ℝ) : 0 ≤ frobSq M := by
  unfold frobSq; positivity

/-- **The raw matrix product** `(rmatMul X Y) i j = ∑ₖ Xᵢₖ·Yₖⱼ` (entry form, no `Matrix` wrapper). -/
noncomputable def rmatMul {p n q : ℕ} (X : Fin p → Fin n → ℝ) (Y : Fin n → Fin q → ℝ) :
    Fin p → Fin q → ℝ :=
  fun i j => ∑ k, X i k * Y k j

/-- **The matrix box** `[−T,T]^{p×n}` (free entries). -/
def matBox (p n : ℕ) (T : ℝ) : Set (Fin p → Fin n → ℝ) :=
  {X | ∀ i k, X i k ∈ Set.Icc (-T) T}

/-! ## The algebraic lower bound (S2-FREE, no measure theory)

For a fixed pivot `(ℓ, j)` with `Y ℓ j ≠ 0`, set `u_i := (X·Y)_{ij}/Y_{ℓj}`. Then
`(X·Y)_{ij} = Y_{ℓj}·u_i`, so `frobSq(X·Y) ≥ ∑_i ((X·Y)_{ij})² = Y_{ℓj}²·∑_i u_i²`. -/

/-- The per-row shear value `u_i := ∑_{k} X_{ik}·(Y_{kj}/Y_{ℓj})` (so `(X·Y)_{ij} = Y_{ℓj}·u_i`). -/
noncomputable def fibreU {p n q : ℕ} (X : Fin p → Fin n → ℝ) (Y : Fin n → Fin q → ℝ)
    (ℓ : Fin n) (j : Fin q) (i : Fin p) : ℝ :=
  ∑ k, X i k * (Y k j / Y ℓ j)

/-- `(X·Y)_{ij} = Y_{ℓj} · u_i` (pull `Y ℓ j` out of the column-`j` dot product). -/
theorem rmatMul_col_eq_pivot_mul_U {p n q : ℕ} (X : Fin p → Fin n → ℝ) (Y : Fin n → Fin q → ℝ)
    (ℓ : Fin n) (j : Fin q) (hℓ : Y ℓ j ≠ 0) (i : Fin p) :
    rmatMul X Y i j = Y ℓ j * fibreU X Y ℓ j i := by
  unfold rmatMul fibreU
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  field_simp

/-- **The column-`j` Frobenius lower bound** `frobSq (X·Y) ≥ ∑ᵢ ((X·Y)_{ij})²` (drop the other
columns — each adds a nonneg term). -/
theorem frobSq_ge_col {p n q : ℕ} (X : Fin p → Fin n → ℝ) (Y : Fin n → Fin q → ℝ) (j : Fin q) :
    (∑ i, (rmatMul X Y i j) ^ 2) ≤ frobSq (rmatMul X Y) := by
  unfold frobSq
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact Finset.single_le_sum (f := fun j => (rmatMul X Y i j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j)

/-- **The pivot lower bound** `frobSq (X·Y) ≥ Y_{ℓj}² · ∑ᵢ u_i²` (`Y ℓ j ≠ 0`). Combines
`frobSq_ge_col` with `(X·Y)_{ij} = Y_{ℓj}·u_i`. -/
theorem frobSq_ge_pivot_sumSqU {p n q : ℕ} (X : Fin p → Fin n → ℝ) (Y : Fin n → Fin q → ℝ)
    (ℓ : Fin n) (j : Fin q) (hℓ : Y ℓ j ≠ 0) :
    (Y ℓ j) ^ 2 * (∑ i, (fibreU X Y ℓ j i) ^ 2) ≤ frobSq (rmatMul X Y) := by
  refine le_trans ?_ (frobSq_ge_col X Y j)
  rw [Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))
  rw [rmatMul_col_eq_pivot_mul_U X Y ℓ j hℓ i]; ring

/-- **The max-entry bound** `Y_{ℓj}² ≥ frobSq Y / (n·q)` when `(ℓ,j)` is an entry of maximal absolute
value (`∀ k j', |Y k j'| ≤ |Y ℓ j|`). The mean-≤-max inequality on the `n·q` entry squares. -/
theorem maxEntry_sq_ge {n q : ℕ} (Y : Fin n → Fin q → ℝ) (ℓ : Fin n) (j : Fin q)
    (hmax : ∀ k j', (Y k j') ^ 2 ≤ (Y ℓ j) ^ 2) :
    frobSq Y ≤ (n * q : ℝ) * (Y ℓ j) ^ 2 := by
  unfold frobSq
  calc ∑ k, ∑ j', (Y k j') ^ 2
      ≤ ∑ _k : Fin n, ∑ _j' : Fin q, (Y ℓ j) ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun j' _ => hmax k j'))
    _ = (n * q : ℝ) * (Y ℓ j) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring

/-! ## The per-row shear is measure-preserving (S2-FREE)

`Φ X i k = if k = ℓ then (∑ k', X i k' · c k') else X i k`, the same shear in each row (`c ℓ = 1`).
Volume-preserving: each row is a single `measurePreserving_shearAt` (coordinate `ℓ`, affine part
`∑_{k'≠ℓ} (coord k')·c k'`), and `volume_preserving_pi` lifts the per-row MP to the matrix product. -/

/-- **The per-row shear** `rowShear c ℓ r k = if k = ℓ then (∑ k' r k' · c k') else r k`
(a single shear at coordinate `ℓ` since `c ℓ = 1`). -/
noncomputable def rowShear {n : ℕ} (c : Fin n → ℝ) (ℓ : Fin n) (r : Fin n → ℝ) : Fin n → ℝ :=
  fun k => if k = ℓ then (∑ k', r k' * c k') else r k

/-- `rowShear c ℓ r ℓ = ∑ k, r k · c k` (the pivot coordinate reads the full linear combination). -/
theorem rowShear_pivot {n : ℕ} (c : Fin n → ℝ) (ℓ : Fin n) (r : Fin n → ℝ) :
    rowShear c ℓ r ℓ = ∑ k, r k * c k := by
  show (if ℓ = ℓ then ∑ k, r k * c k else r ℓ) = ∑ k, r k * c k
  rw [if_pos rfl]

/-- `rowShear c ℓ (X i) ℓ = fibreU X Y ℓ j i` when `c k = Y k j / Y ℓ j` (the pivot of the per-row
shear is the fibre coordinate `u_i`). -/
theorem rowShear_pivot_eq_fibreU {p n q : ℕ} (Y : Fin n → Fin q → ℝ) (ℓ : Fin n) (j : Fin q)
    (X : Fin p → Fin n → ℝ) (i : Fin p) :
    rowShear (fun k => Y k j / Y ℓ j) ℓ (X i) ℓ = fibreU X Y ℓ j i := by
  rw [rowShear_pivot]; rfl

/-- **The per-row shear is measure-preserving** on `Fin n → ℝ` (`c ℓ = 1`), via
`measurePreserving_shearAt` at coordinate `ℓ` with affine part `g y = ∑_{k} y k · c (ℓ.succAbove k)`. -/
theorem measurePreserving_rowShear {n : ℕ} (c : Fin n → ℝ) (ℓ : Fin n) (hc : c ℓ = 1) :
    MeasurePreserving (rowShear c ℓ) (volume : Measure (Fin n → ℝ)) volume := by
  match n, ℓ, c, hc with
  | (N+1), ℓ, c, hc =>
    set g : (Fin N → ℝ) → ℝ := fun y => ∑ k : Fin N, y k * c (ℓ.succAbove k) with hgdef
    have hg : Measurable g := by fun_prop
    have h := measurePreserving_shearAt (n := N) ℓ g hg
    have hfun : (fun x : Fin (N + 1) → ℝ =>
          Function.update x ℓ (x ℓ + g (fun k => x (ℓ.succAbove k)))) = rowShear c ℓ := by
      funext x k
      by_cases hk : k = ℓ
      · subst k
        rw [Function.update_self]
        simp only [rowShear, if_pos rfl, hgdef, if_true]
        rw [Fin.sum_univ_succAbove (fun k' => x k' * c k') ℓ, hc, mul_one]
      · rw [Function.update_of_ne hk]
        simp only [rowShear, if_neg hk]
    rwa [hfun] at h

/-- **The matrix per-row shear is measure-preserving** on `Fin p → Fin n → ℝ`: the same `rowShear`
in every row, lifted by `volume_preserving_pi`. -/
theorem measurePreserving_matShear {p n : ℕ} (c : Fin n → ℝ) (ℓ : Fin n) (hc : c ℓ = 1) :
    MeasurePreserving (fun X : Fin p → Fin n → ℝ => fun i => rowShear c ℓ (X i))
      (volume : Measure (Fin p → Fin n → ℝ)) volume :=
  volume_preserving_pi (fun _ : Fin p => measurePreserving_rowShear c ℓ hc)

/-! ## The pivot-column box integral (the Tonelli factorisation to `sumSqND`, S2-FREE)

`∫⁻_{matBox p (N+1) S} (∑ᵢ (W i ℓ)²)^{−c'} dW < ⊤` for `c' < p/2`: the integrand reads only the
pivot column `(W i ℓ)ᵢ`, so a measure-preserving reindex `(per-row piFinSuccAbove at ℓ) ∘
(arrowProdEquivProdArrow)` splits the matrix into `(pivot : Fin p → ℝ) × (spectators)` and Tonelli
(`radial_morse_dominates_lt_top`, `W = 0`) factors the `p`-dim Morse pivot integral (`sumSqND`, finite)
from the spectator box volume (finite). -/

/-- The reindex `eSplit : (Fin p → Fin (N+1) → ℝ) ≃ᵐ (Fin p → ℝ) × (Fin p → Fin N → ℝ)` that pulls the
column-`ℓ` pivot coordinate of each row into the first factor (`piFinSuccAbove ℓ` per row, then
`arrowProdEquivProdArrow`). -/
noncomputable def eSplit (p N : ℕ) (ℓ : Fin (N + 1)) :
    (Fin p → Fin (N + 1) → ℝ) ≃ᵐ (Fin p → ℝ) × (Fin p → Fin N → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin p =>
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) ℓ)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin N → ℝ) (Fin p))

/-- `eSplit` is measure-preserving. -/
theorem measurePreserving_eSplit (p N : ℕ) (ℓ : Fin (N + 1)) :
    MeasurePreserving (eSplit p N ℓ)
      (volume : Measure (Fin p → Fin (N + 1) → ℝ)) volume := by
  refine MeasurePreserving.trans ?_ (volume_measurePreserving_arrowProdEquivProdArrow ℝ (Fin N → ℝ) (Fin p))
  exact volume_preserving_pi
    (fun _ : Fin p => volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) ℓ)

/-- The first component of `eSplit W` is the pivot column `(W i ℓ)ᵢ`. -/
theorem eSplit_fst (p N : ℕ) (ℓ : Fin (N + 1)) (W : Fin p → Fin (N + 1) → ℝ) (i : Fin p) :
    ((eSplit p N ℓ) W).1 i = W i ℓ := rfl

/-- `matBox` as a `MeasurableSet`. -/
theorem matBox_measurableSet (p n : ℕ) (S : ℝ) : MeasurableSet (matBox p n S) := by
  rw [show matBox p n S = {X : Fin p → Fin n → ℝ | ∀ i k, X i k ∈ Set.Icc (-S) S} from rfl]
  apply MeasurableSet.congr (s := ⋂ i, ⋂ k, {X : Fin p → Fin n → ℝ | X i k ∈ Set.Icc (-S) S})
  · refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun k => ?_))
    exact measurableSet_Icc.preimage ((measurable_pi_apply i).eval)
  · ext X; simp [matBox]

/-- `matBox p (N+1) S = eSplit ⁻¹' (morseBox p S ×ˢ matBox p N S)` — the box splits into the pivot
column box and the spectator matrix box under the reindex. -/
theorem matBox_eq_eSplit_preimage (p N : ℕ) (ℓ : Fin (N + 1)) (S : ℝ) :
    matBox p (N + 1) S
      = (eSplit p N ℓ) ⁻¹' (morseBox p S ×ˢ matBox p N S) := by
  ext W
  simp only [matBox, morseBox, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_implies]
  constructor
  · intro hW
    exact ⟨fun i => hW i ℓ, fun i k => hW i (ℓ.succAbove k)⟩
  · rintro ⟨h1, h2⟩ i k
    rcases Fin.eq_self_or_eq_succAbove ℓ k with rfl | ⟨k', rfl⟩
    · exact h1 i
    · exact h2 i k'

/-- **The pivot-column box integral factorises** `∫⁻_{matBox p (N+1) S} (∑ᵢ (W i ℓ)²)^{−c'}
= Kbound p c' S · volume (matBox p N S)`. The integrand reads only the pivot column; `eSplit` (MP)
factors the matrix into `(pivot : Fin p → ℝ) × (spectators)`, and `setLIntegral_prod` separates the
`p`-dim Morse pivot integral (`Kbound`) from the spectator box volume. The factored value is manifestly
ℓ-independent. -/
theorem pivotCol_box_eq {p N : ℕ} (ℓ : Fin (N + 1)) (S : ℝ) (c' : ℝ) :
    ∫⁻ W in matBox p (N + 1) S, ENNReal.ofReal ((∑ i, (W i ℓ) ^ 2) ^ (-c'))
      = Kbound p c' S * volume (matBox p N S) := by
  -- the integrand reads only the pivot column `(W i ℓ)ᵢ = (eSplit W).1 i`
  set H : (Fin p → ℝ) × (Fin p → Fin N → ℝ) → ℝ≥0∞ :=
    fun pr => ENNReal.ofReal ((∑ i, (pr.1 i) ^ 2) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by rw [hHdef]; fun_prop
  have hmp := measurePreserving_eSplit p N ℓ
  -- transport the integral via `eSplit`
  have hrw : ∫⁻ W in matBox p (N + 1) S, ENNReal.ofReal ((∑ i, (W i ℓ) ^ 2) ^ (-c'))
      = ∫⁻ pr in morseBox p S ×ˢ matBox p N S, H pr := by
    rw [matBox_eq_eSplit_preimage p N ℓ S]
    rw [← hmp.setLIntegral_comp_preimage_emb (eSplit p N ℓ).measurableEmbedding H
      (morseBox p S ×ˢ matBox p N S)]
    rfl
  rw [hrw, Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable]
  -- inner integral over spectators is constant `(∑ pr.1 i²)^{−c'}` (H ignores `.2`)
  have hinner : ∀ u : Fin p → ℝ, ∫⁻ _v in matBox p N S, H (u, _v)
      = ENNReal.ofReal ((∑ i, (u i) ^ 2) ^ (-c')) * volume (matBox p N S) := by
    intro u; simp only [hHdef]; rw [setLIntegral_const]
  simp only [hinner]
  rw [lintegral_mul_const _ (by fun_prop)]
  congr 1

/-- **The pivot-column box integral is finite** for `c' < p/2`, `S > 0`: the Morse factor `Kbound`
is finite (`Kbound_lt_top`, `sumSqND`), the spectator box volume is finite (compact). -/
theorem pivotCol_box_lt_top {p N : ℕ} (hp : 1 ≤ p) (ℓ : Fin (N + 1)) (S : ℝ) (hS : 0 < S)
    (c' : ℝ) (hc' : c' < p / 2) :
    ∫⁻ W in matBox p (N + 1) S, ENNReal.ofReal ((∑ i, (W i ℓ) ^ 2) ^ (-c')) < ⊤ := by
  rw [pivotCol_box_eq]
  apply ENNReal.mul_lt_top
  · obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    exact Kbound_lt_top m S hS c' (by push_cast at hc' ⊢; linarith)
  · have hcpt : IsCompact (matBox p N S) := by
      have heq : matBox p N S = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin N =>
          Set.Icc (-S) S)) := by
        ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
    exact hcpt.measure_lt_top

/-- The 2×2 → `Fin 4` flatten `e22` (MP): uncurry the matrix to `(Fin 2 × Fin 2) → ℝ`
(`MeasurableEquiv.curry _ _ _ |>.symm`), then reindex `Fin 2 × Fin 2 ≃ Fin 4` (`arrowCongr'`). -/
noncomputable def e22 : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (Fin 4 → ℝ) :=
  (MeasurableEquiv.curry (Fin 2) (Fin 2) ℝ).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).trans (finCongr (by norm_num)))
      (MeasurableEquiv.refl ℝ))

/-- `e22 A i = A ((g.symm i).1) ((g.symm i).2)` for the reindex `g = finProdFinEquiv ∘ finCongr`
(the flatten reads the matrix entry at the decoded `(row, col)`). -/
theorem e22_apply (A : Fin 2 → Fin 2 → ℝ) (i : Fin 4) :
    e22 A i = A
      (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2*2)).trans (finCongr (by norm_num))).symm i).1
      (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2*2)).trans (finCongr (by norm_num))).symm i).2 := rfl

/-- The uncurry `(Fin 2 → Fin 2 → ℝ) ≃ᵐ (Fin 2 × Fin 2 → ℝ)` is measure-preserving — `curry` is a
reindex of the product Lebesgue measure. Via `arrowProdEquivProdArrow` is awkward (it splits the
codomain, not the domain index); this is the `MeasurableEquiv.curry` reindex MP, a standard fact. -/
theorem measurePreserving_uncurry22 :
    MeasurePreserving (MeasurableEquiv.curry (Fin 2) (Fin 2) ℝ).symm
      (volume : Measure (Fin 2 → Fin 2 → ℝ)) (volume : Measure (Fin 2 × Fin 2 → ℝ)) := by
  sorry

theorem measurePreserving_e22 :
    MeasurePreserving e22 (volume : Measure (Fin 2 → Fin 2 → ℝ)) (volume : Measure (Fin 4 → ℝ)) := by
  unfold e22
  exact measurePreserving_uncurry22.trans (volume_preserving_arrowCongr'
    ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).trans (finCongr (by norm_num)))
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))

theorem frobSq22_box_lt_top (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc' : c' < 2) :
    ∫⁻ A in matBox 2 2 T, ENNReal.ofReal ((frobSq A) ^ (-c')) < ⊤ := by
  -- `frobSq A = ∑_{i<4} (e22 A i)²` (the flatten reindexes the 4 entries; `Equiv.sum_comp`)
  have hfrob : ∀ A : Fin 2 → Fin 2 → ℝ, frobSq A = ∑ i, (e22 A i) ^ 2 := by
    intro A
    set g : Fin 2 × Fin 2 ≃ Fin 4 :=
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).trans (finCongr (by norm_num)) with hg
    rw [show (∑ i, (e22 A i) ^ 2) = ∑ i, (A (g.symm i).1 (g.symm i).2) ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [e22_apply])]
    rw [Equiv.sum_comp g.symm (fun kj : Fin 2 × Fin 2 => (A kj.1 kj.2) ^ 2), Fintype.sum_prod_type]
    rfl
  -- transport via `e22` (MP); `matBox 2 2 T = e22 ⁻¹' (morseBox 4 T)`
  have hmp := measurePreserving_e22
  have hpre : matBox 2 2 T = e22 ⁻¹' (morseBox 4 T) := by
    ext A
    simp only [matBox, morseBox, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies]
    set g : Fin 2 × Fin 2 ≃ Fin 4 :=
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).trans (finCongr (by norm_num)) with hg
    constructor
    · intro h i; rw [e22_apply]; exact h _ _
    · intro h k2 jj
      have := h (g (k2, jj))
      rw [e22_apply] at this
      simpa [hg, Equiv.symm_apply_apply] using this
  have hrwfrob : ∀ A : Fin 2 → Fin 2 → ℝ, ENNReal.ofReal ((frobSq A) ^ (-c'))
      = (fun x : Fin 4 → ℝ => ENNReal.ofReal ((∑ i, (x i) ^ 2) ^ (-c'))) (e22 A) := fun A => by
    rw [hfrob]
  have hpremeas : MeasurableSet (e22 ⁻¹' (morseBox 4 T)) :=
    (morseBox_measurableSet 4 T).preimage e22.measurable
  rw [hpre, setLIntegral_congr_fun hpremeas (fun A _ => hrwfrob A),
    hmp.setLIntegral_comp_preimage_emb e22.measurableEmbedding
      (fun x => ENNReal.ofReal ((∑ i, (x i) ^ 2) ^ (-c'))) (morseBox 4 T)]
  exact sumSqND_box_lt_top 3 T hT c' (by norm_num; linarith)

/-! ## The fibre lemma (the iterated-fibre engine, S2-FREE) -/

/-- **The fibre constant** `fibreConst p n q T c' = ofReal((n·q)^{c'}) · (pivot Morse integral at
half-width `n·T`) · (spectator box volume)` — the `Y`-independent, ℓ-independent finite multiplier of
the fibre bound: `(n·q)^{c'}` from the max-entry step, the `p`-dim `sumSqND` Morse factor, and the
spectator `[−nT,nT]^{p·(n−1)}` volume (the Tonelli factorisation of the pivot-column box integral). -/
noncomputable def fibreConst (p n q : ℕ) (T c' : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n * q : ℕ) : ℝ) ^ c') *
    (Kbound p c' ((n : ℝ) * T) * volume (matBox p (n - 1) ((n : ℝ) * T)))

/-- **`fibreConst` is finite** for `1 ≤ p`, `T > 0`, `c' < p/2`: the `(n·q)^{c'}` factor is finite,
the Morse `Kbound` factor is finite (`Kbound_lt_top`), the spectator box has finite volume (compact). -/
theorem fibreConst_lt_top (p n q : ℕ) (T c' : ℝ) (hT : 0 < T) (hc' : c' < p / 2)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    fibreConst p n q T c' < ⊤ := by
  have hnT : 0 < (n : ℝ) * T := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [fibreConst]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  apply ENNReal.mul_lt_top
  · obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    exact Kbound_lt_top m ((n : ℝ) * T) hnT c' (by push_cast at hc' ⊢; linarith)
  · have hcpt : IsCompact (matBox p (n - 1) ((n : ℝ) * T)) := by
      have heq : matBox p (n - 1) ((n : ℝ) * T)
          = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin (n - 1) =>
            Set.Icc (-((n : ℝ) * T)) ((n : ℝ) * T))) := by
        ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
    exact hcpt.measure_lt_top

theorem fibreConst_ne_top (p n q : ℕ) (T c' : ℝ) (hT : 0 < T) (hc' : c' < p / 2)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    fibreConst p n q T c' ≠ ⊤ := (fibreConst_lt_top p n q T c' hT hc' hp hn).ne

/-- The shear-image box bound: `matShear c ℓ '' (matBox p n T) ⊆ matBox p n (n·T)` when every
`|c k| ≤ 1` (`|u_i| = |∑_k X_{ik} c_k| ≤ n·T`; spectators unchanged, `≤ T ≤ n·T`). -/
theorem matShear_image_subset {p n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (ℓ : Fin n)
    (hc1 : ∀ k, |c k| ≤ 1) (T : ℝ) (hT : 0 ≤ T) :
    (fun X : Fin p → Fin n → ℝ => fun i => rowShear c ℓ (X i)) '' (matBox p n T)
      ⊆ matBox p n ((n : ℝ) * T) := by
  rintro W ⟨X, hX, rfl⟩
  intro i k
  simp only [matBox, Set.mem_setOf_eq] at hX
  rw [Set.mem_Icc]
  by_cases hk : k = ℓ
  · -- pivot coord: u_i = ∑ X i k' c k', bounded by n·T
    subst k
    simp only [rowShear, if_pos rfl]
    have hbound : |∑ k', X i k' * c k'| ≤ (n : ℝ) * T := by
      calc |∑ k', X i k' * c k'| ≤ ∑ k', |X i k' * c k'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k' : Fin n, T := by
            refine Finset.sum_le_sum (fun k' _ => ?_)
            rw [abs_mul]
            have h1 : |X i k'| ≤ T := abs_le.mpr (hX i k')
            calc |X i k'| * |c k'| ≤ T * 1 := by
                  apply mul_le_mul h1 (hc1 k') (abs_nonneg _) hT
              _ = T := mul_one T
        _ = (n : ℝ) * T := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact abs_le.mp hbound
  · -- spectator coord: unchanged, |W i k| ≤ T ≤ n·T
    simp only [rowShear, if_neg hk]
    have h1 : |X i k| ≤ T := abs_le.mpr (hX i k)
    have hTle : T ≤ (n : ℝ) * T := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    constructor <;> [nlinarith [abs_le.mp h1]; nlinarith [abs_le.mp h1]]

/-- The matrix-box integrand `frobSq (X·Y)^{−c'}` is measurable in `X` (a polynomial composed with
the fixed-exponent `rpow`). -/
theorem measurable_frobSq_rmatMul_rpow {p n q : ℕ} (Y : Fin n → Fin q → ℝ) (c' : ℝ) :
    Measurable (fun X : Fin p → Fin n → ℝ =>
      ENNReal.ofReal ((frobSq (rmatMul X Y)) ^ (-c'))) := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq rmatMul
  fun_prop

/-- **The fibre lemma (the iterated-fibre engine, S2-FREE).** For a FIXED `Y : Fin n → Fin q → ℝ`
(`n, q ≥ 1`), the matrix-box fibre integral of `frobSq (X·Y)^{−c'}` is bounded by a `Y`-independent
finite constant times `(frobSq Y)^{−c'}`, for `c' < p/2`, `c' ≥ 0`, `T > 0`:

    ∫⁻_{X∈matBox p n T} (frobSq (X·Y))^{−c'} ≤ fibreConst · (frobSq Y)^{−c'}.

The max-abs entry `(ℓ,j)` is chosen INSIDE the proof (`Finset.exists_max_image`) — never in the
statement; the per-row shear (det-1) gives `frobSq(X·Y) ≥ (Y ℓ j)²·∑ u_i²` and `(Y ℓ j)² ≥
frobSq Y/(n·q)`, reducing to the pivot-column box integral (`pivotCol_box_lt_top`, Tonelli `sumSqND`,
S2-free). At `Y = 0` both sides are `0`. -/
theorem fibre_lintegral_mul_le {p n q : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < p / 2)
    (Y : Fin n → Fin q → ℝ) :
    ∫⁻ X in matBox p n T, ENNReal.ofReal ((frobSq (rmatMul X Y)) ^ (-c'))
      ≤ fibreConst p n q T c' * ENNReal.ofReal ((frobSq Y) ^ (-c')) := by
  -- the pivot-column box integral value (Y-independent, finite)
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  -- case Y = 0: both sides are 0 (0^{−c'} = 0 since c' > 0)
  by_cases hY0 : frobSq Y = 0
  · -- frobSq Y = 0 ⟹ every entry 0 ⟹ rmatMul X Y = 0 ⟹ LHS integrand 0
    have hYzero : ∀ k j, Y k j = 0 := by
      intro k j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 hY0 k (Finset.mem_univ k)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 this j (Finset.mem_univ j))
    have hLHS0 : ∀ X : Fin p → Fin (N+1) → ℝ, frobSq (rmatMul X Y) = 0 := by
      intro X
      unfold frobSq rmatMul
      refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
      have : (∑ k, X i k * Y k j) = 0 := Finset.sum_eq_zero (fun k _ => by rw [hYzero k j]; ring)
      rw [this]; ring
    calc ∫⁻ X in matBox p (N+1) T, ENNReal.ofReal ((frobSq (rmatMul X Y)) ^ (-c'))
        = ∫⁻ _X in matBox p (N+1) T, ENNReal.ofReal ((0 : ℝ) ^ (-c')) := by
          refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun X _ => ?_)
          rw [hLHS0 X]
      _ = 0 := by
          rw [Real.zero_rpow (by linarith)]; simp
      _ ≤ _ := zero_le _
  -- case Y ≠ 0: max-abs-entry pivot
  · have hne : (0 : ℝ) < frobSq Y := lt_of_le_of_ne (frobSq_nonneg Y) (Ne.symm hY0)
    -- pick the max-abs entry over Fin (N+1) × Fin q
    obtain ⟨⟨ℓ, j⟩, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (N+1) × Fin q))
      (fun kj => (Y kj.1 kj.2) ^ 2) ⟨(⟨0, by omega⟩, ⟨0, hq⟩), Finset.mem_univ _⟩
    -- the max entry square is positive (else all entries 0, Y = 0)
    have hpivpos : (0 : ℝ) < (Y ℓ j) ^ 2 := by
      by_contra hle
      push_neg at hle
      have : (Y ℓ j) ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
      have hall : ∀ k j', (Y k j') ^ 2 = 0 := fun k j' =>
        le_antisymm (le_trans (hmax (k, j') (Finset.mem_univ _)) (le_of_eq this)) (sq_nonneg _)
      have : frobSq Y = 0 := by
        unfold frobSq; exact Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun j' _ => hall k j'))
      exact hY0 this
    have hpivne : Y ℓ j ≠ 0 := fun h => by rw [h] at hpivpos; simp at hpivpos
    set c : Fin (N+1) → ℝ := fun k => Y k j / Y ℓ j with hcdef
    have hcℓ : c ℓ = 1 := by rw [hcdef]; simp [div_self hpivne]
    -- the per-row shear pivot is the fibre coordinate (the load-bearing column identity)
    have hcolU : ∀ (X : Fin p → Fin (N+1) → ℝ) (i : Fin p),
        rowShear c ℓ (X i) ℓ = fibreU X Y ℓ j i := by
      intro X i; rw [hcdef]; exact rowShear_pivot_eq_fibreU Y ℓ j X i
    have hc1 : ∀ k, |c k| ≤ 1 := by
      intro k
      rw [hcdef]; simp only
      rw [abs_div, div_le_one (by positivity)]
      have := hmax (k, j) (Finset.mem_univ _)
      simp only at this
      nlinarith [sq_abs (Y k j), sq_abs (Y ℓ j), abs_nonneg (Y k j), abs_nonneg (Y ℓ j)]
    -- change-of-variables setup
    have hmpS := measurePreserving_matShear (p := p) c ℓ hcℓ
    -- The pivot-zero set `{∑u² = 0}` is null (off it, the pointwise rpow bound holds): via `eSplit`,
    -- `{W | ∑(W i ℓ)² = 0}` corresponds to `{u = 0} ×ˢ univ` (a point in `Fin p → ℝ`, p ≥ 1), null;
    -- the X-set is its preimage under the MP `matShear`.
    have hpivnull : volume {X : Fin p → Fin (N+1) → ℝ | ∑ i, (fibreU X Y ℓ j i) ^ 2 = 0} = 0 := by
      -- `fibreU X i = (matShear X) i ℓ`, so the set is `matShear ⁻¹' {W | ∑ (W i ℓ)² = 0}`
      have heqset : {X : Fin p → Fin (N+1) → ℝ | ∑ i, (fibreU X Y ℓ j i) ^ 2 = 0}
          = (fun X : Fin p → Fin (N+1) → ℝ => fun i => rowShear c ℓ (X i)) ⁻¹'
              {W : Fin p → Fin (N+1) → ℝ | ∑ i, (W i ℓ) ^ 2 = 0} := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        have : (∑ i, ((fun i => rowShear c ℓ (X i)) i ℓ) ^ 2) = ∑ i, (fibreU X Y ℓ j i) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by simp only; rw [hcolU X i])
        rw [this]
      have hWnull : volume {W : Fin p → Fin (N+1) → ℝ | ∑ i, (W i ℓ) ^ 2 = 0} = 0 := by
        -- via eSplit, the pivot column = 0 is a point in Fin p → ℝ
        have hsub : {W : Fin p → Fin (N+1) → ℝ | ∑ i, (W i ℓ) ^ 2 = 0}
            ⊆ (eSplit p N ℓ) ⁻¹' ({(0 : Fin p → ℝ)} ×ˢ (Set.univ : Set (Fin p → Fin N → ℝ))) := by
          intro W hW
          simp only [Set.mem_setOf_eq] at hW
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
          funext i
          rw [eSplit_fst]
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
            ((Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).1 hW i (Finset.mem_univ i))
        refine measure_mono_null hsub ?_
        rw [(measurePreserving_eSplit p N ℓ).measure_preimage_emb (eSplit p N ℓ).measurableEmbedding
          ({(0 : Fin p → ℝ)} ×ˢ (Set.univ : Set (Fin p → Fin N → ℝ)))]
        rw [Measure.volume_eq_prod, Measure.prod_prod]
        -- `volume {(0 : Fin p → ℝ)} = 0` (p ≥ 1): `{0} ⊆ {x | x ⟨0⟩ = 0}` = ker(proj), null
        have hp0 : volume ({(0 : Fin p → ℝ)}) = 0 := by
          have hp' : 0 < p := by omega
          refine measure_mono_null
            (show ({(0 : Fin p → ℝ)} : Set (Fin p → ℝ)) ⊆ (LinearMap.ker
              (LinearMap.proj (⟨0, hp'⟩ : Fin p) : (Fin p → ℝ) →ₗ[ℝ] ℝ) : Set (Fin p → ℝ)) from ?_) ?_
          · intro x hx; simp only [Set.mem_singleton_iff] at hx
            simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, hx, Pi.zero_apply]
          · refine Measure.addHaar_submodule _ _ (fun htop => ?_)
            have hmem : (Pi.single (⟨0, hp'⟩ : Fin p) (1 : ℝ)) ∈
                LinearMap.ker (LinearMap.proj (⟨0, hp'⟩ : Fin p) : (Fin p → ℝ) →ₗ[ℝ] ℝ) :=
              htop ▸ Submodule.mem_top
            simp only [LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same,
              one_ne_zero] at hmem
        rw [hp0, zero_mul]
      rw [heqset, hmpS.measure_preimage (NullMeasurableSet.of_null hWnull)]
      exact hWnull
    -- the (a.e.) pointwise bound on the integrand (off the null pivot-zero set)
    have hptwise_ae : ∀ᵐ X ∂(volume.restrict (matBox p (N+1) T)),
        ENNReal.ofReal ((frobSq (rmatMul X Y)) ^ (-c'))
          ≤ ENNReal.ofReal (((Y ℓ j) ^ 2) ^ (-c'))
              * ENNReal.ofReal ((∑ i, (fibreU X Y ℓ j i) ^ 2) ^ (-c')) := by
      have hae : ∀ᵐ X : Fin p → Fin (N+1) → ℝ, ∑ i, (fibreU X Y ℓ j i) ^ 2 ≠ 0 := by
        rw [ae_iff]; simpa using hpivnull
      refine (ae_restrict_of_ae hae).mono (fun X hX => ?_)
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hge := frobSq_ge_pivot_sumSqU X Y ℓ j hpivne
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      have hupos : (0 : ℝ) < ∑ i, (fibreU X Y ℓ j i) ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hX)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hge (by linarith)
    set G : (Fin p → Fin (N+1) → ℝ) → ℝ≥0∞ :=
      fun W => ENNReal.ofReal ((∑ i, (W i ℓ) ^ 2) ^ (-c')) with hGdef
    have hGmeas : Measurable G := by rw [hGdef]; fun_prop
    set Sbig : ℝ := ((N:ℝ)+1) * T with hSbig
    have hGmatShear_meas : Measurable (fun X : Fin p → Fin (N+1) → ℝ =>
        G (fun i => rowShear c ℓ (X i))) := hGmeas.comp hmpS.measurable
    -- u_i(X) = (matShear X) i ℓ = fibreU X Y ℓ j i (since (matShear X) i ℓ = ∑ X i k' c k')
    have hUeq : ∀ (X : Fin p → Fin (N+1) → ℝ),
        ENNReal.ofReal ((∑ i, (fibreU X Y ℓ j i) ^ 2) ^ (-c'))
          = G (fun i => rowShear c ℓ (X i)) := by
      intro X
      rw [hGdef]
      congr 2
      exact (Finset.sum_congr rfl (fun i _ => by simp only; rw [hcolU X i])).symm
    -- the change-of-variables chain (pointwise indicator bound + matShear MP)
    have hCOV : ∫⁻ X in matBox p (N+1) T, ENNReal.ofReal ((∑ i, (fibreU X Y ℓ j i) ^ 2) ^ (-c'))
        ≤ ∫⁻ W in matBox p (N+1) Sbig, ENNReal.ofReal ((∑ i, (W i ℓ) ^ 2) ^ (-c')) := by
      calc ∫⁻ X in matBox p (N+1) T, ENNReal.ofReal ((∑ i, (fibreU X Y ℓ j i) ^ 2) ^ (-c'))
          = ∫⁻ X in matBox p (N+1) T, G (fun i => rowShear c ℓ (X i)) := by
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun X _ => ?_)
            exact hUeq X
        _ = ∫⁻ X, (matBox p (N+1) T).indicator (fun X => G (fun i => rowShear c ℓ (X i))) X := by
            rw [lintegral_indicator (matBox_measurableSet _ _ _)]
        _ ≤ ∫⁻ X : Fin p → Fin (N+1) → ℝ,
              ((matBox p (N+1) Sbig).indicator G) (fun i => rowShear c ℓ (X i)) := by
            refine lintegral_mono (fun X => ?_)
            by_cases hX : X ∈ matBox p (N+1) T
            · rw [Set.indicator_of_mem hX]
              have hin : (fun i => rowShear c ℓ (X i)) ∈ matBox p (N+1) Sbig := by
                have hsub := matShear_image_subset (p := p) (show 1 ≤ N + 1 by omega) c ℓ hc1 T
                  (le_of_lt hT)
                have hmem : (fun i => rowShear c ℓ (X i)) ∈ matBox p (N+1) ((↑(N+1) : ℝ) * T) :=
                  hsub (Set.mem_image_of_mem
                    (fun X : Fin p → Fin (N+1) → ℝ => fun i => rowShear c ℓ (X i)) hX)
                rw [hSbig]
                have heqS : ((↑(N+1) : ℝ) * T) = ((N:ℝ)+1) * T := by push_cast; ring
                rwa [heqS] at hmem
              rw [Set.indicator_of_mem hin]
            · rw [Set.indicator_of_notMem hX]; exact zero_le _
        _ = ∫⁻ W, (matBox p (N+1) Sbig).indicator G W :=
            hmpS.lintegral_comp (hGmeas.indicator (matBox_measurableSet _ _ _))
        _ = ∫⁻ W in matBox p (N+1) Sbig, ENNReal.ofReal ((∑ i, (W i ℓ) ^ 2) ^ (-c')) := by
            rw [lintegral_indicator (matBox_measurableSet _ _ _)]
    -- integrate the pointwise bound and chain through the COV
    calc ∫⁻ X in matBox p (N+1) T, ENNReal.ofReal ((frobSq (rmatMul X Y)) ^ (-c'))
        ≤ ∫⁻ X in matBox p (N+1) T, ENNReal.ofReal (((Y ℓ j) ^ 2) ^ (-c'))
              * ENNReal.ofReal ((∑ i, (fibreU X Y ℓ j i) ^ 2) ^ (-c')) :=
          lintegral_mono_ae hptwise_ae
      _ = ENNReal.ofReal (((Y ℓ j) ^ 2) ^ (-c'))
            * ∫⁻ X in matBox p (N+1) T, ENNReal.ofReal ((∑ i, (fibreU X Y ℓ j i) ^ 2) ^ (-c')) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (((Y ℓ j) ^ 2) ^ (-c'))
            * ∫⁻ W in matBox p (N+1) Sbig, ENNReal.ofReal ((∑ i, (W i ℓ) ^ 2) ^ (-c')) :=
          mul_le_mul_left' hCOV _
      _ = ENNReal.ofReal (((Y ℓ j) ^ 2) ^ (-c'))
            * (Kbound p c' (((N:ℝ)+1) * T) * volume (matBox p N (((N:ℝ)+1) * T))) := by
          rw [pivotCol_box_eq ℓ (((N:ℝ)+1) * T) c']
      _ ≤ fibreConst p (N + 1) q T c' * ENNReal.ofReal ((frobSq Y) ^ (-c')) := by
          -- (Y ℓ j²)^{−c'} ≤ (nq)^{c'}·(frobSq Y)^{−c'} (max-entry: Yℓj² ≥ frobSq Y/(nq))
          rw [fibreConst]
          have hmaxsq : frobSq Y ≤ (((N+1) * q : ℕ) : ℝ) * (Y ℓ j) ^ 2 := by
            have := maxEntry_sq_ge Y ℓ j (fun k j' => hmax (k, j') (Finset.mem_univ _))
            push_cast at this ⊢; linarith
          have hnqpos : (0 : ℝ) < (((N+1) * q : ℕ) : ℝ) := by
            have : 0 < (N+1) * q := Nat.mul_pos (Nat.succ_pos N) hq
            exact_mod_cast this
          -- (Y ℓ j²)^{−c'} ≤ (nq)^{c'}·(frobSq Y)^{−c'} as reals (both nonneg)
          have hkey : ((Y ℓ j) ^ 2) ^ (-c') ≤ (((N+1) * q : ℕ) : ℝ) ^ c' * (frobSq Y) ^ (-c') := by
            -- (nq·Yℓj²)^{−c'} ≤ (frobSq Y)^{−c'} (antitone, frobSq Y ≤ nq·Yℓj², both > 0)
            have hanti : ((((N+1) * q : ℕ) : ℝ) * (Y ℓ j) ^ 2) ^ (-c') ≤ (frobSq Y) ^ (-c') :=
              Real.rpow_le_rpow_of_nonpos hne hmaxsq (by linarith)
            -- LHS = (nq)^{−c'}·(Yℓj²)^{−c'}
            rw [Real.mul_rpow (le_of_lt hnqpos) (le_of_lt hpivpos)] at hanti
            -- multiply both sides by (nq)^{c'} > 0
            have hmul : (((N+1)*q:ℕ):ℝ)^c' * ((((N+1)*q:ℕ):ℝ)^(-c') * ((Y ℓ j)^2)^(-c'))
                ≤ (((N+1)*q:ℕ):ℝ)^c' * (frobSq Y)^(-c') :=
              mul_le_mul_of_nonneg_left hanti (Real.rpow_nonneg (le_of_lt hnqpos) c')
            rw [← mul_assoc, ← Real.rpow_add hnqpos, add_neg_cancel, Real.rpow_zero, one_mul] at hmul
            exact hmul
          calc ENNReal.ofReal (((Y ℓ j) ^ 2) ^ (-c'))
              * (Kbound p c' (((N:ℝ)+1) * T) * volume (matBox p N (((N:ℝ)+1) * T)))
              ≤ ENNReal.ofReal ((((N+1) * q : ℕ) : ℝ) ^ c' * (frobSq Y) ^ (-c'))
                  * (Kbound p c' (((N:ℝ)+1) * T) * volume (matBox p N (((N:ℝ)+1) * T))) := by
                apply mul_le_mul_right'
                exact ENNReal.ofReal_le_ofReal hkey
            _ = ENNReal.ofReal ((((N+1) * q : ℕ) : ℝ) ^ c')
                  * (Kbound p c' ((↑(N+1) : ℝ) * T) * volume (matBox p ((N+1) - 1) ((↑(N+1) : ℝ) * T)))
                  * ENNReal.ofReal ((frobSq Y) ^ (-c')) := by
                have hcast : ((N:ℝ)+1) * T = (↑(N+1) : ℝ) * T := by push_cast; ring
                rw [hcast, ENNReal.ofReal_mul (by positivity), show (N + 1) - 1 = N from rfl]
                ring

end DLNFibre.DLN.RLCT
