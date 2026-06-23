import DLNFibre.DLN.RLCT.Validate.DeepestMinRlct
import DLNFibre.DLN.RLCT.Foundations.S1Fubini

/-!
# `DLNFibre.DLN.RLCT.Validate.BoxThresholdBridge` — the box→point RLCT collapse (#11, R1 bridge)

The **`BoxThresholdBridge`**: for a measurable `F` whose deepest point is the global-minimum local
RLCT, every exponent `c'` below the deepest point's threshold makes `|F|^{−c'}` integrable over any
**compact** box `Vz`. This is the side-fact the R1 cover GE leg consumes (the
`chart_pullback_lt_top` family, `fm3/routem-ga-transport`): its per-chart child box-integrability
`hKint = IntegrableOn |K|^{−c'} Vz` is exactly this bridge applied to the child core `K`, with
antecedent `c' < rlctAtOn K 0`.

## The honest split (Proved / Reused / Cited)

- **PROVED here** (cite-free, the genuinely-new layer): the finite-subcover collapse
  `box_integrable_of_lt_rlctAtOn_deepest` — `c' < rlctAtOn F deepest` together with the *ordering*
  `∀ p, rlctAtOn F deepest ≤ rlctAtOn F p` gives, per point of the compact `Vz`, an integrable open
  neighbourhood (`rlctAtOn` is the `sSup` of admissible exponents with such a neighbourhood;
  `lt_sSup` extraction + the admissible-down-set `admissible_downset`), hence
  `LocallyIntegrableOn` on `Vz`, hence `IntegrableOn` by compactness
  (`LocallyIntegrableOn.integrableOn_isCompact`).
- **REUSED** (proven, `DeepestMinRlct`): the *ordering* is value-free — for a degree-`D` homogeneous
  `F`, `deepest_le_of_homogeneous_core` gives `rlctAtOn F 0 ≤ rlctAtOn F v` for every `v` (the
  all-zero point is the cone vertex sitting in every zero-product stratum's closure, so its local
  RLCT is the minimum). `dlnLoss M 0` is degree-`2L` homogeneous (`dlnLoss_zero_smul`), so the
  ordering holds for the true loss at every node — closing the flagged "load-bearing open" piece.
- **NOT here** (cite-free): the *value* `rlctAtOn deepest = ½·minAdm` is the cover's S2-only job
  (the spine + atom), established separately. This bridge is **value-agnostic** — it talks only of
  the *relative* threshold `rlctAtOn F 0`, never `Mval`/`minAdm`/`rlct = ½·mval`. So the headline
  stays "proven modulo only S2", and the bridge is non-circular.

Axiom target: only `propext` / `Classical.choice` / `Quot.sound`.
-/

open MeasureTheory Set ENNReal
open scoped Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The homogeneity of the true loss (`dlnLoss M 0` is degree-`2L`) -/

/-- The layer-product fold scales `prodAux H (c • A) k = c^k • prodAux H A k`: each of the `k`
folded layer matrices pulls out one factor `c`. -/
theorem prodAux_smul (H : Fin (L + 1) → ℕ) (A : Params H) (c : ℝ) (k : ℕ) (hk : k < L + 1) :
    prodAux H (fun s => c • A s) k hk = c ^ k • prodAux H A k hk := by
  induction k with
  | zero => change (1 : Matrix _ _ ℝ) = c ^ 0 • 1; rw [pow_zero, one_smul]
  | succ k ih =>
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      have hcast : ((by rw [e1, e2]; exact (fun s => c • A s) ⟨k, hkL⟩ :
            Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ))
          = c • ((by rw [e1, e2]; exact A ⟨k, hkL⟩ :
            Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) := by
        cases e1; cases e2; rfl
      have lhs : prodAux H (fun s => c • A s) (k + 1) hk
          = prodAux H (fun s => c • A s) k hk' *
              ((by rw [e1, e2]; exact (fun s => c • A s) ⟨k, hkL⟩ :
                Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) := rfl
      have rhs : prodAux H A (k + 1) hk
          = prodAux H A k hk' *
              ((by rw [e1, e2]; exact A ⟨k, hkL⟩ :
                Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) := rfl
      rw [lhs, ih, hcast, rhs, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ]

/-- The multiplication map is degree-`L` homogeneous: `prod H (c • A) = c^L • prod H A`. -/
theorem prod_smul (H : Fin (L + 1) → ℕ) (A : Params H) (c : ℝ) :
    prod H (fun s => c • A s) = c ^ L • prod H A := by
  rw [prod, prod]; exact prodAux_smul H A c L (Nat.lt_succ_self L)

/-- **The true loss `dlnLoss M 0` is degree-`2L` homogeneous.**
`dlnLoss H 0 (c • A) = c^(2L)·dlnLoss H 0 A` — the multiplication map is degree-`L` homogeneous
(`prod_smul`) and the loss squares it. Supplies the homogeneity hypothesis downstream. -/
theorem dlnLoss_zero_smul (H : Fin (L + 1) → ℕ) (A : Params H) (c : ℝ) :
    dlnLoss H 0 (fun s => c • A s) = c ^ (2 * L) * dlnLoss H 0 A := by
  simp only [dlnLoss, sub_zero, prod_smul, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_pow, ← pow_mul]
  ring

/-! ## The box→point integrability collapse (the cite-free finite-subcover layer) -/

/-- **The box-threshold bridge (abstract, ordering form).** For a measurable `F` on a proper space
with locally-finite volume, whose `deepest` point has the minimum local RLCT (`hmin`), every
exponent `c'` below the deepest threshold makes `|F|^{−c'}` integrable over any **compact** `Vz`.

Proof: `c' < rlctAtOn F deepest ≤ rlctAtOn F p` for each `p ∈ Vz` (`hmin`); since `rlctAtOn F p` is
the `sSup` of admissible exponents (each with an open neighbourhood of `p` on which `|F|^{−·}` is
integrable), `lt_sSup` yields an admissible `c'' > c'`, and `admissible_downset` descends to `c'`,
giving an integrable open neighbourhood of `p`. So `|F|^{−c'}` is `LocallyIntegrableOn` on `Vz`,
hence `IntegrableOn` on the compact `Vz`. -/
theorem box_integrable_of_lt_rlctAtOn_deepest {M : Type*}
    [PseudoMetricSpace M] [MeasureSpace M] [ProperSpace M]
    [IsFiniteMeasureOnCompacts (volume : Measure M)] [OpensMeasurableSpace M]
    [TopologicalSpace.PseudoMetrizableSpace M]
    (F : M → ℝ) (hFmeas : Measurable F) (deepest : M)
    (hmin : ∀ p, rlctAtOn F deepest ≤ rlctAtOn F p)
    (Vz : Set M) (hVz : IsCompact Vz) (c' : NNReal)
    (hc' : (c' : ENNReal) < rlctAtOn F deepest) :
    IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume := by
  have hloc : ∀ p ∈ Vz, ∃ Ω : Set M, IsOpen Ω ∧ p ∈ Ω ∧
      IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Ω volume := by
    intro p _
    have hcp : (c' : ENNReal) < rlctAtOn F p := lt_of_lt_of_le hc' (hmin p)
    obtain ⟨c, hcS, hc'c⟩ := lt_sSup_iff.1 (by unfold rlctAtOn weightedThreshold at hcp; exact hcp)
    obtain ⟨c'', rfl, Ω, hΩopen, hpΩ, hint⟩ := hcS
    have hc'lt : (c' : ℝ) ≤ (c'' : ℝ) := by exact_mod_cast le_of_lt (by exact_mod_cast hc'c)
    exact admissible_downset F hFmeas p (c' : ℝ) (c'' : ℝ) (by positivity) hc'lt
      ⟨Ω, hΩopen, by simpa using hpΩ, by simpa using hint⟩
  have hLI : LocallyIntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume := by
    intro p hp
    obtain ⟨Ω, hΩopen, hpΩ, hint⟩ := hloc p hp
    exact ⟨Ω, mem_nhdsWithin_of_mem_nhds (hΩopen.mem_nhds hpΩ), hint⟩
  exact hLI.integrableOn_isCompact hVz

/-- **The box-threshold bridge for a homogeneous `F` (compact form).** For any degree-`D`
homogeneous `F` on `Fin N → ℝ`, every exponent `c'` below the *origin* threshold `rlctAtOn F 0`
makes `|F|^{−c'}` integrable over any compact `Vz`. The ordering hypothesis of the abstract bridge
is discharged value-free by `deepest_le_of_homogeneous_core` (the all-zero cone vertex is the
global-min RLCT). A homogeneous `F` of the relevant shape is the flattened true loss `dlnLoss M 0`
(`dlnLoss_zero_smul` gives degree `2L` on `Params`); e.g. the `(2,2,2)` flattened core `‖A·B‖²` on
`Fin 8 → ℝ` (`Case222Resolution.myF222`), with `rlctAtOn · 0 = 3/2`. -/
theorem box_integrable_of_lt_rlctAtOn_zero_of_homogeneous {N : ℕ}
    (F : (Fin N → ℝ) → ℝ) (D : ℕ) (hFmeas : Measurable F)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w)
    (Vz : Set (Fin N → ℝ)) (hVz : IsCompact Vz) (c' : NNReal)
    (hc' : (c' : ENNReal) < rlctAtOn F (0 : Fin N → ℝ)) :
    IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume :=
  box_integrable_of_lt_rlctAtOn_deepest F hFmeas 0
    (fun p => deepest_le_of_homogeneous_core F p D hFmeas hhomog) Vz hVz c' hc'

/-- **The `BoxThresholdBridge` predicate (bounded-measurable form) for a homogeneous `F`.** The
shape the R1 cover consumer wants: over any **bounded measurable** box `Vz` (not necessarily
compact), `c' < rlctAtOn F 0` makes `|F|^{−c'}` integrable. On `Fin N → ℝ` (proper) the bounded `Vz`
has compact closure (`Bornology.IsBounded.isCompact_closure`); the compact-form bridge gives
integrability on `closure Vz`, restricted to `Vz` by `IntegrableOn.mono_set subset_closure`.
`MeasurableSet Vz` is carried to match the consumer predicate verbatim (the proof routes through the
larger closure, so it is not used for integrability itself). -/
theorem box_integrable_of_lt_rlctAtOn_zero_of_homogeneous_of_bounded {N : ℕ}
    (F : (Fin N → ℝ) → ℝ) (D : ℕ) (hFmeas : Measurable F)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w)
    (Vz : Set (Fin N → ℝ)) (_hVzm : MeasurableSet Vz) (hVzbdd : Bornology.IsBounded Vz)
    (c' : NNReal) (hc' : (c' : ENNReal) < rlctAtOn F (0 : Fin N → ℝ)) :
    IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume :=
  (box_integrable_of_lt_rlctAtOn_zero_of_homogeneous F D hFmeas hhomog (closure Vz)
    hVzbdd.isCompact_closure c' hc').mono_set subset_closure

end DLNFibre.DLN.RLCT
