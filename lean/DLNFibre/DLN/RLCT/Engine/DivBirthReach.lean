import DLNFibre.DLN.RLCT.Engine.NumDivFlatBound

/-!
# `DLNFibre.DLN.RLCT.Engine.DivBirthReach` — the `divCoord`-injectivity reachability invariant

The divisor→flat-slot map `divCoord` at a leaf sends each `t̃=0` analytic divisor to its **immutable
birth corner** `(s_birth, J_birth, J_birth)` — the diagonal corner of the birth layer's weight matrix
(slot-stability cert, `threads/17-slot-stability/cert-slot-stability.md`). This module threads the
reachability invariant that makes that map WELL-TYPED and INJECTIVE, so the ChartBridge per-leaf
clauses `Function.Injective divCoord` can be discharged.

**The invariant `DivBirthInv`** bundles, for every divisor `k` of a reachable state `s`:
* **validity** — the stored corner `(a, b) = divBirthCoord k` has `a < L`, `b < M⁽ᵃ⁾` (row bound) and
  `b < M⁽ᵃ⁺¹⁾` (col bound); these are exactly the `Fin`-coercion side-conditions `flatCoordOf` needs;
* **layer bound** — `a ≤ layer` (a divisor is born at or below the current layer);
* **freshness** — a corner at the CURRENT layer has `b < cleared` (its column was cleared strictly
  before the current cleared count), the inductive strengthening that makes births append a corner
  distinct from every stored one;
* **injectivity** — `divBirthCoord` is injective (pairwise-distinct corners, cert §4: 0 within-state
  collisions).

**Battery-verified** (slot-stability cert §4): across `(2,2,2),(3,3,4),(2,2,2,2),(2,2,3,2)`,
`(3,3,2,2),(2,2,3,3,2)` and the audit instances, births never rewrite an existing slot and no two
live divisors share a slot. The proof mirrors `NumDivFlatBound`: `conRoot` base (vacuous, `numDiv=0`),
the three state-level transition-maintenance lemmas, and the `conOracle`-navigation fold.

**Accounting.** A birth (`stepAppendAdvance`) appends the corner `(layer, cleared)` (the OLD cleared,
before the `+1` advance): validity from the append guard `cleared < widthMinUpto (layer+1)`, which is
`≤ M⁽ˡᵃʸᵉʳ⁾` and `≤ M⁽ˡᵃʸᵉʳ⁺¹⁾`; distinctness from freshness (every stored corner at `layer` has `<
cleared`, so `≠ (layer, cleared)`). `stepCase11` carries all fields verbatim (congruence); rollover
(`layer += 1, cleared := 0`) keeps the ledger and re-establishes freshness vacuously (all stored
layers `≤ old layer < new layer`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The corner-validity predicate + the threaded invariant -/

/-- **A birth corner `(a, b)` is valid** for `M`: the birth layer `a` is a real layer (`a < L`) and
the diagonal column `b` fits both the row width `M⁽ᵃ⁾` and the column width `M⁽ᵃ⁺¹⁾`. Phrased with
`∀ i, (i:ℕ) = a → …` (proof-irrelevant) so the two `M`-bounds extract at any `Fin (L+1)` index of
the right value — exactly what the `flatCoordOf` `Fin` coercions need. -/
def CornerValid (M : Fin (L + 1) → ℕ) (c : ℕ × ℕ) : Prop :=
  c.1 < L ∧ (∀ i : Fin (L + 1), (i : ℕ) = c.1 → c.2 < M i) ∧
    (∀ i : Fin (L + 1), (i : ℕ) = c.1 + 1 → c.2 < M i)

/-- **The birth-corner reachability invariant**: validity + layer-bound + freshness + injectivity of
`divBirthCoord`, threaded down the construction. Freshness is the inductive strengthening that keeps
each birth's fresh corner distinct from every stored one. -/
def DivBirthInv (M : Fin (L + 1) → ℕ) (s : ConState L) : Prop :=
  (∀ k : Fin s.numDiv, CornerValid M (s.divBirthCoord k)) ∧
    (∀ k : Fin s.numDiv, (s.divBirthCoord k).1 ≤ s.layer) ∧
      (∀ k : Fin s.numDiv, (s.divBirthCoord k).1 = s.layer → (s.divBirthCoord k).2 < s.cleared) ∧
        Function.Injective s.divBirthCoord

/-- `DivBirthInv` at the root (`numDiv = 0`): every clause is vacuous. -/
theorem DivBirthInv_conRoot {M : Fin (L + 1) → ℕ} : DivBirthInv M (conRoot : ConState L) := by
  refine ⟨fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, ?_⟩
  intro a; exact a.elim0

/-! ## State-level per-transition maintenance (given the dispatch guards) -/

/-- Case-1(1) merge leaves `layer`/`cleared`/`numDiv`/`divBirthCoord` unchanged — `DivBirthInv`
transfers by defeq. -/
theorem DivBirthInv_stepCase11 {M : Fin (L + 1) → ℕ} (s : ConState L) (i : Fin s.numDiv)
    (h : DivBirthInv M s) : DivBirthInv M (s.stepCase11 i) := h

/-- Rollover (`layer += 1, cleared := 0`, ledger carried) preserves `DivBirthInv`. Validity and
injectivity carry verbatim (`divBirthCoord`/`M` unchanged); the layer-bound relaxes by one;
freshness is vacuous (every stored corner has layer `≤ old layer < new layer`). -/
theorem DivBirthInv_stepRollover {M : Fin (L + 1) → ℕ} (s : ConState L)
    (h : DivBirthInv M s) : DivBirthInv M s.stepRollover := by
  obtain ⟨hvalid, hlayerLE, _, hinj⟩ := h
  refine ⟨hvalid, ?_, ?_, hinj⟩
  · intro k
    have := hlayerLE k
    change (s.divBirthCoord k).1 ≤ s.layer + 1
    omega
  · intro k hk
    have h1 : (s.divBirthCoord k).1 = s.layer + 1 := hk
    have := hlayerLE k
    omega

/-- Case-1(2)/case-2 birth (`numDiv += 1, cleared += 1`, `layer` fixed, `divBirthCoord` snocs the
fresh corner `(layer, cleared)`) preserves `DivBirthInv`, given the append guards `layer < L` and
`cleared < widthMinUpto (layer+1)` (the `conOracle` non-terminal, non-rollover branch). -/
theorem DivBirthInv_stepAppendAdvance {M : Fin (L + 1) → ℕ} (s : ConState L) (e : ℕ)
    (t₀ : Fin L → ℕ) (hlive : s.layer < L)
    (hlt : s.cleared < widthMinUpto M (s.layer + 1)) (h : DivBirthInv M s) :
    DivBirthInv M (s.stepAppendAdvance e t₀) := by
  obtain ⟨hvalid, hlayerLE, hfresh, hinj⟩ := h
  -- The fresh corner (layer, cleared) is valid: its column `cleared` fits both adjacent widths.
  have hnewvalid : CornerValid M (s.layer, s.cleared) := by
    refine ⟨hlive, ?_, ?_⟩
    · intro i hi; exact lt_of_lt_of_le hlt (widthMinUpto_le i (by omega))
    · intro i hi; exact lt_of_lt_of_le hlt (widthMinUpto_le i (by omega))
  -- The fresh corner is not among the stored ones (freshness).
  have hnotmem : (s.layer, s.cleared) ∉ Set.range s.divBirthCoord := by
    rintro ⟨j, hj⟩
    have h1 : (s.divBirthCoord j).1 = s.layer := by rw [hj]
    have h2 : (s.divBirthCoord j).2 = s.cleared := by rw [hj]
    exact absurd (hfresh j h1) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    induction k using Fin.lastCases with
    | last => simpa [ConState.stepAppendAdvance, Fin.snoc_last] using hnewvalid
    | cast j => simpa [ConState.stepAppendAdvance, Fin.snoc_castSucc] using hvalid j
  · intro k
    induction k using Fin.lastCases with
    | last =>
      simp only [ConState.stepAppendAdvance, Fin.snoc_last, le_refl]
    | cast j =>
      simp only [ConState.stepAppendAdvance, Fin.snoc_castSucc]
      exact hlayerLE j
  · intro k
    induction k using Fin.lastCases with
    | last =>
      intro _; simp only [ConState.stepAppendAdvance, Fin.snoc_last]; omega
    | cast j =>
      simp only [ConState.stepAppendAdvance, Fin.snoc_castSucc]
      intro hj
      have := hfresh j hj
      omega
  · change Function.Injective (Fin.snoc s.divBirthCoord (s.layer, s.cleared))
    exact Fin.snoc_injective_of_injective hinj hnotmem

/-! ## The `conOracle`-navigation maintenance (the isolated crux) -/

/-- **`DivBirthInv` maintenance through `conOracle`'s step-children** — mirrors
`NumDivInv_conOracle_stepChildren`: reduce each `conOracle` dispatch branch to its `StepChild`'s
state + guards, then apply the matching state-level maintenance lemma. -/
theorem DivBirthInv_conOracle_stepChildren {M : Fin (L + 1) → ℕ} (s : ConState L)
    (inv : DivBirthInv M s) (c : StepChild M s) (hc : c ∈ (conOracle M s).stepChildren) :
    DivBirthInv M c.child := by
  by_cases h1 : L ≤ s.layer
  · have horacle : conOracle M s = oracleTerminal M s := by unfold conOracle; rw [dif_pos h1]
    rw [horacle] at hc
    simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hc
  · have hlive : s.layer < L := not_le.mp h1
    by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle M s = rolloverDecision M s (le_of_lt (not_le.mp h1)) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [horacle] at hc
      simp only [rolloverDecision, ConDecision.stepChildren, List.mem_singleton] at hc
      subst hc
      exact DivBirthInv_stepRollover s inv
    · have hlt : s.cleared < widthMinUpto M (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap M := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap M _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · -- case-2
        have horacle : conOracle M s = case2Decision M s
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [horacle] at hc
        simp only [case2Decision, ConDecision.stepChildren, List.mem_singleton] at hc
        subst hc
        exact DivBirthInv_stepAppendAdvance s _ _ hlive hlt inv
      · rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle M s = oracleTerminal M s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [horacle] at hc
          simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hc
        · -- case-1 (two children: stepCase11, then stepAppendAdvance)
          have hgt : s.cleared < target := by
            obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff'.mp hmin
            rw [List.mem_filterMap] at hmemtar
            obtain ⟨k0, -, hk0⟩ := hmemtar
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
            · rw [if_pos hc0] at hk0
              have hdt : s.divTilde k0 = target := Option.some.inj hk0
              omega
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          have horacle : conOracle M s = case1Decision M s f (target - s.cleared)
              (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared)
              (not_le.mp h1) (by omega) (by rw [(chooseMin_spec s target hf).1]; omega) hcap := by
            unfold conOracle
            rw [dif_neg h1, dif_neg h2]
            split
            · rename_i target' heq
              obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)
              split
              · rename_i f' hf'
                obtain rfl : f' = f := Option.some.inj (hf' ▸ hf)
                rfl
              · rename_i hf'
                exact absurd (hf' ▸ hf) (by simp)
            · rename_i heq
              exact absurd (heq ▸ hmin) (by simp)
          rw [horacle] at hc
          simp only [case1Decision, ConDecision.stepChildren, List.mem_cons,
            List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact DivBirthInv_stepCase11 s f inv
          · exact DivBirthInv_stepAppendAdvance s _ _ hlive hlt inv

end DLNFibre.DLN.RLCT.Engine
