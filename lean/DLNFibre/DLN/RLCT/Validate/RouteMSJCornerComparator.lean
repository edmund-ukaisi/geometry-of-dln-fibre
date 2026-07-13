import DLNFibre.DLN.RLCT.Validate.RouteMSJAdm
import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplit

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCornerComparator` — the reduced comparator (S1, #5 peelOp target)

**Thread `genm-sj5` (#5 `DecoratedStepHyp`, S1 — the reduced-comparator producibility).** The S0-corrected
`#5` peel CLOSES by DOMINATION, not weld (`s0-reduced-core-fidelity-cert.md`): the parent box integral is
dominated by a CONSTANT times the integral of a genuinely-admissible reduced decoration `D'` carrying the
CLEAN reduced-product loss `commonDivisor(u)² · frobSq (prod M')`, which the decorated IH then closes. This
module supplies that comparator `D'` and PROVES it `adm`-admissible — the "reduced-adm producibility"
deliverable the controller routes a soundness review over BEFORE the domination builds on it.

`cornerComparator M' k jc` is the general form of the base-leg non-vacuity witness `witnessDecoration222`,
now carrying `genuineCarrier` (the clause `witnessDecoration222` left un-asserted, flagged as `#5`'s own
obligation): its deeper space IS `Params M'` and its `ctx` reads the honest layer product `prod M'`, so
`genuineCarrier` holds with `e = id`. Its resolved-corner `FaithfulSJAt` clause is discharged via the head
split (`RouteMSJHeadSplit`): the free front block is the leading layer `A 0`, the tied tail is
`prod (dropHead M')`, and the residual provenance `prod M' = rmatMul (A 0) (prod (dropHead M'))` is the
banked front-peel (`prod_headSplit`). The dims clause `minAdm M' ≤ a · M' 1` is the head bound
`minAdm_le_mul_head` at the FORCED faithful row-count `a = M' 0`.

* **`cornerComparator M' k jc`** — the reduced comparator on `M' : Fin (L+1+1) → ℕ`, `d`-fold uniform
  support `≡ k`, accumulated Jacobian `jc`; `ν = ι = Fin (M' 0) × Fin (M' last)`, identity-selection carrier
  (`residual = prod M'` entry), deeper space `Params M'`, `ctx = prod M'`, domain the parameter box.
* **`cornerComparator_decLoss`** — `decLoss u z = commonDivisor(u)² · frobSq (prod M' z)` (the clean loss).
* **`cornerComparator_adm`** — GIVEN the β threshold `½·minAdm M' ≤ monomialThreshold d k jc` and `1 ≤ d`,
  `adm (L+1) M' (cornerComparator M' k jc)`: `genuineCarrier` (`e = id`) ∧ `FaithfulSJAt` (γ' via head-split).
* **`exists_cornerComparator_adm`** — non-vacuity: the β threshold is satisfiable (`d = 1`, `k ≡ 1`,
  `jc = minAdm M' − 1`), so an admissible reduced comparator EXISTS on every `M'`.

S2-FREE: the banked carrier algebra + head-split + `minAdm` bounds. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators Matrix

variable {L : ℕ}

/-! ## The reduced comparator decoration -/

/-- **The reduced comparator decoration** on `M' : Fin (L+1+1) → ℕ`: `d`-fold uniform exceptional support
`≡ k`, accumulated Jacobian `jc`; active/generator index `Fin (M' 0) × Fin (M' last)`, identity-selection
carrier (generator `ik`'s residual reads off the `ik` entry of the active input), deeper space `Params M'`,
`ctx` supplying the honest layer product `prod M'`, domain the parameter box `paramsBoxM M' 1`. Its loss is
`commonDivisor(u)² · frobSq (prod M')`. -/
noncomputable def cornerComparator (M' : Fin (L + 1 + 1) → ℕ) (k jc : Fin d → ℕ) :
    SJDecoration M' where
  d := d
  ζ := Unit
  ν := Fin (M' 0) × Fin (M' (Fin.last (L + 1)))
  ι := Fin (M' 0) × Fin (M' (Fin.last (L + 1)))
  fν := inferInstance
  fι := inferInstance
  carrier :=
    ({ supp := fun _ ℓ => k ℓ
       coeff := fun _ ik i'k' => if i'k' = ik then 1 else 0 } :
      SJLinGenState Unit (Fin (M' 0) × Fin (M' (Fin.last (L + 1))))
        (Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) d)
  jac := jc
  Z := Params M'
  mZ := inferInstance
  ctx := fun A => ((), fun ik => prod M' A ik.1 ik.2)
  dom := paramsBoxM M' 1
  residualMeas := by
    intro ik
    haveI : OpensMeasurableSpace (Params M') :=
      inferInstanceAs (OpensMeasurableSpace
        (∀ s : Fin (L + 1), Fin (M' s.castSucc) → Fin (M' s.succ) → ℝ))
    have hcont : Continuous fun A : Params M' => prod M' A ik.1 ik.2 :=
      (continuous_prod M').matrix_elem ik.1 ik.2
    simp only [SJLinGenState.residual, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hcont.measurable

/-! ## The comparator's residual, support, and loss -/

/-- The comparator's residual reads off the layer-product entry: `residual _ (prod M' A ·) ik
= prod M' A ik.1 ik.2`. -/
theorem cornerComparator_residual (M' : Fin (L + 1 + 1) → ℕ) (k jc : Fin d → ℕ)
    (A : Params M') (ik : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) :
    letI := (cornerComparator M' k jc).fν
    (cornerComparator M' k jc).carrier.residual ((cornerComparator M' k jc).ctx A).1
        ((cornerComparator M' k jc).ctx A).2 ik = prod M' A ik.1 ik.2 := by
  letI := (cornerComparator M' k jc).fν
  simp only [cornerComparator, SJLinGenState.residual, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The comparator's exceptional support is uniform `≡ k`, so its shared-divisor exponent is `k`. -/
theorem cornerComparator_sharedDivisorExp (M' : Fin (L + 1 + 1) → ℕ) (k jc : Fin d → ℕ)
    (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) :
    letI := (cornerComparator M' k jc).fι
    letI : Nonempty (cornerComparator M' k jc).ι := ⟨i₀⟩
    sharedDivisorExp (cornerComparator M' k jc).carrier.supp = k := by
  letI := (cornerComparator M' k jc).fι
  letI : Nonempty (cornerComparator M' k jc).ι := ⟨i₀⟩
  funext ℓ
  unfold sharedDivisorExp
  refine le_antisymm ?_ ?_
  · exact Finset.inf'_le _ (Finset.mem_univ i₀)
  · exact Finset.le_inf' _ _ (fun i _ => le_refl _)

/-- **The comparator's decorated loss is the clean reduced-product loss**
`decLoss u z = commonDivisor(u)² · frobSq (prod M' z)`. The identity-selection carrier makes each residual
the product entry; the uniform support factors `commonDivisor(u)` out of every generator; the sum of
squares reassembles `frobSq (prod M' z)`. -/
theorem cornerComparator_decLoss (M' : Fin (L + 1 + 1) → ℕ) (k jc : Fin d → ℕ)
    (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) (u : Fin d → ℝ) (z : Params M') :
    letI := (cornerComparator M' k jc).fι
    letI := (cornerComparator M' k jc).fν
    letI : Nonempty (cornerComparator M' k jc).ι := ⟨i₀⟩
    (cornerComparator M' k jc).decLoss u z
      = commonDivisor (cornerComparator M' k jc).carrier.supp u ^ 2 * frobSq (prod M' z) := by
  letI := (cornerComparator M' k jc).fι
  letI := (cornerComparator M' k jc).fν
  letI : Nonempty (cornerComparator M' k jc).ι := ⟨i₀⟩
  unfold SJDecoration.decLoss SJLinGenState.loss
  rw [show frobSq (prod M' z)
      = ∑ ik : Fin (M' 0) × Fin (M' (Fin.last (L + 1))), (prod M' z ik.1 ik.2) ^ 2 by
    rw [frobSq, Fintype.sum_prod_type], Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ik _ => ?_)
  rw [SJLinGenState.gen_eq, cornerComparator_residual]
  have hmon : genMonomial (cornerComparator M' k jc).carrier.supp ik u
      = commonDivisor (cornerComparator M' k jc).carrier.supp u := by
    unfold genMonomial commonDivisor
    refine Finset.prod_congr rfl (fun ℓ _ => ?_)
    congr 1
    exact (le_antisymm (sharedDivisorExp_le _ ik ℓ)
      (Finset.le_inf' _ _ (fun i _ => le_refl _))).symm
  rw [hmon]; ring

/-! ## `genuineCarrier` for the comparator (`e = id`) -/

/-- **The comparator is a genuine carrier** (`e = id`). Its deeper space IS `Params M'`, `ν` is the product
index type, `ctx` reads the layer product `prod M'`. The clause `witnessDecoration222` left un-asserted —
here discharged, since the comparator's `Z` is `Params M'` outright (no split needed for `genuineCarrier`). -/
theorem cornerComparator_genuineCarrier (M' : Fin (L + 1 + 1) → ℕ) (k jc : Fin d → ℕ) :
    genuineCarrier (cornerComparator M' k jc) := by
  refine ⟨rfl, rfl, MeasurableEquiv.refl (Params M'), ?_, ?_, fun z => rfl⟩
  · exact MeasurePreserving.id (volume : Measure (Params M'))
  · ext A; rfl

/-! ## `FaithfulSJAt` for the comparator (γ' via the head split) -/

/-- **The comparator satisfies `FaithfulSJAt`** (the `d ≥ 1` resolved-corner disjunct), given `1 ≤ d` and
the β threshold `½·minAdm M' ≤ monomialThreshold d k jc`. The clauses:
* **α** (`pSimultaneous`) — uniform support: every generator attains the shared minimum `k` everywhere.
* **β** — the supplied threshold hypothesis (`sharedDivisorExp = k`).
* **δ≡0** — uniform support: `supp i ℓ = sharedDivisorExp _ ℓ = k ℓ`.
* **γ'** — the front block is the leading layer `A 0` (`a = M' 0`, via the head split `paramsHeadSplit`);
  the tied tail is `prod (dropHead M')`; the provenance `residual = rmatMul (A 0) (prod (dropHead M'))`
  is the banked front-peel `prod_headSplit`; `ρ = id`; the dims clause `minAdm M' ≤ (M' 0) · M' 1` is
  `minAdm_le_mul_head`; the domain-box split is `paramsHeadSplit_preimage_box`. -/
theorem cornerComparator_faithful (M' : Fin (L + 1 + 1) → ℕ) (k jc : Fin d → ℕ) (hd : 1 ≤ d)
    (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1))))
    (hbeta : (minAdm M' : ℝ≥0∞) / 2
      ≤ monomialThreshold d k jc) :
    FaithfulSJAt (cornerComparator M' k jc) := by
  letI := (cornerComparator M' k jc).fι
  letI := (cornerComparator M' k jc).fν
  haveI : Nonempty (cornerComparator M' k jc).ι := ⟨i₀⟩
  have hk : sharedDivisorExp (cornerComparator M' k jc).carrier.supp = k :=
    cornerComparator_sharedDivisorExp M' k jc i₀
  refine Or.inr ⟨hd, i₀, ?_, ?_, ?_, ?_⟩
  · -- (α) pSimultaneous: uniform support.
    intro j ℓ; exact le_refl _
  · -- (β) threshold: the supplied hypothesis (`sharedDivisorExp = k`).
    rw [hk]; exact hbeta
  · -- (δ≡0) uniform support.
    intro i ℓ
    show k ℓ = sharedDivisorExp (cornerComparator M' k jc).carrier.supp ℓ
    rw [hk]
  · -- (γ') provenance via the head split.
    refine ⟨M' 0, paramsHeadSplit M', Equiv.refl _, paramsHeadSplit_mp M', ?_, ?_, ?_⟩
    · -- domain-box split.
      show (cornerComparator M' k jc).dom
        = paramsHeadSplit M' ⁻¹' (matBox (M' 0) (M' 1) 1 ×ˢ paramsBoxM (dropHead M') 1)
      rw [paramsHeadSplit_preimage_box]; rfl
    · -- dims clause `minAdm M' ≤ (M' 0) · M' 1`.
      exact minAdm_le_mul_head M'
    · -- the residual provenance `residual = rmatMul (A 0) (prod (dropHead M'))`.
      intro z i
      rw [cornerComparator_residual]
      show prod M' z i.1 i.2
        = rmatMul (paramsHeadSplit M' z).1 (prod (dropHead M') (paramsHeadSplit M' z).2) i.1 i.2
      rw [paramsHeadSplit_fst]
      have hsplit := prod_headSplit M' z
      calc prod M' z i.1 i.2
          = rmatMul (z 0) (prod (dropHead M') (fun j => z j.succ)) i.1 i.2 := by rw [hsplit]
        _ = rmatMul (paramsHeadSplit M' z).1 (prod (dropHead M') (paramsHeadSplit M' z).2) i.1 i.2 :=
            rfl

/-! ## The full `adm` admissibility + non-vacuity -/

/-- **The reduced comparator is `adm`-admissible** (the S1 producibility deliverable). Given `1 ≤ d` and the
β threshold, `adm (L+1) M' (cornerComparator M' k jc)`: `genuineCarrier` ∧ `FaithfulSJAt` (the third `adm`
disjunct). This is the genuinely-admissible reduced decoration `D'` the S0-corrected domination hands to the
decorated IH. -/
theorem cornerComparator_adm (M' : Fin (L + 1 + 1) → ℕ) (k jc : Fin d → ℕ) (hd : 1 ≤ d)
    (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1))))
    (hbeta : (minAdm M' : ℝ≥0∞) / 2 ≤ monomialThreshold d k jc) :
    adm (L + 1) M' (cornerComparator M' k jc) :=
  ⟨cornerComparator_genuineCarrier M' k jc,
    cornerComparator_faithful M' k jc hd i₀ hbeta⟩

/-- **Non-vacuity: an admissible reduced comparator EXISTS on every `M'` with inhabited endpoint index.**
The β threshold is satisfiable
at the clean single-radial choice `d = 1`, `k ≡ 1`, `jc = minAdm M' − 1`: then `monomialThreshold 1 ![1]
![minAdm M' − 1] = axisRatio (minAdm M' − 1) 1 = minAdm M' / 2` (binding equality), so
`½·minAdm M' ≤ monomialThreshold`. Guards against a silently-vacuous comparator: the reduced-decoration
producibility is genuine (`adm` is met by a concrete `D'`). -/
theorem exists_cornerComparator_adm (M' : Fin (L + 1 + 1) → ℕ)
    (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) :
    ∃ (k jc : Fin 1 → ℕ), adm (L + 1) M' (cornerComparator M' k jc) := by
  refine ⟨![1], ![minAdm M' - 1], cornerComparator_adm M' ![1] ![minAdm M' - 1] (le_refl 1) i₀ ?_⟩
  rw [monomialThreshold_eq_iInf_axisRatio]
  refine le_iInf (fun j => ?_)
  have hk1 : (![1] : Fin 1 → ℕ) j = 1 := by simp [Matrix.cons_val_fin_one]
  have hjc : (![minAdm M' - 1] : Fin 1 → ℕ) j = minAdm M' - 1 := by simp [Matrix.cons_val_fin_one]
  rw [hk1, hjc]
  rcases Nat.eq_zero_or_pos (minAdm M') with hm0 | hmpos
  · rw [hm0]; simp
  · rw [show minAdm M' - 1 = (minAdm M' - 1 + 1) - 1 from by omega,
      axisRatio_regularSeq (minAdm M' - 1 + 1) (by omega),
      show minAdm M' - 1 + 1 = minAdm M' from by omega]

end DLNFibre.DLN.RLCT
