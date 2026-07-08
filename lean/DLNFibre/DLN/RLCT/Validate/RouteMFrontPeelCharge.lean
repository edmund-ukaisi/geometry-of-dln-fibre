import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMFrontPeelCharge` — the FRONT-PEEL identity for `minAdm`

The pure-ℕ combinatorial closure of the sub-generic strata (wall R1-UPPER, cert
`expeditions/2026-06-20-aoyagi-full/threads/genm-r1substratum/cert.md`). Where the banked
`minAdm_cons_eq` peels the leading TWO widths at a pivot rank `t ≤ min(M₀,M₁)`, the **front-peel**
peels the leading SINGLE width `M₀` against the whole tail product `P` (widths `(M₁,…,M_L)`),
stratified by `rank P = q ≤ min(M₁,…,M_L)`:

    minAdm (M₀,M₁,…,M_L)  =  min_{q ≤ min(M₁,…,M_L)} [ M₀·q + minAdm (M₁−q, M₂−q, …, M_L−q) ]   (FP)

The `M₀·q` term is the codim of `{A₀·(q-dim column space of P) = 0}`; the shifted-tail `minAdm` is
the codim of `{rank P ≤ q}`. Exact-verified (0-fail exhaustive ≈12k chains widths ≤12, adversarial,
permutation-invariant, term-by-term = the paper's Voight/Ext orbit codimension; cert §C).

The identity holds for `≥ 3`-width chains (`Fin (L+1+1+1)`): the tail `(M₁,…,M_L)` must itself be a
genuine `≥ 2`-width product-chain. Statement:
- `frontCharge_ge_minAdm` — the front-peel inequality (`minAdm M ≤ frontCharge M q` at every admissible `q`);
- `minAdm_eq_frontPeel` — the min over `q` is achieved (`(FP)`).

Proof architecture (fully de-risked numerically, no permutation-invariance):
- `twoVar_min_eq` — a 2-variable elementary min identity (reflection `q = b − t`, clamped witnesses).
- an arity induction: expand `minAdm M` by the LAYER-peel (`sjChargeBudget_*`), apply the front-peel
  IH to the reduced chains, and close each direction with a witness supplied by `twoVar_min_eq`.
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The 2-variable core identity (reflection `q = b − t`, clamped witnesses) -/

/-- **The 2-variable min identity.** `min_{t ≤ min(a,b)} [(a−t)(b−t) + t·r] = min_{q ≤ min(r,b)}
[a·q + (b−q)(r−q)]`. Under the reflection `q = b − t` the summands coincide
(`a(b−t)+(t)(r−b+t) = (a−t)(b−t)+t r`); the two integer ranges differ, so each `inf'` is bounded by
the other via a clamped witness (`q = min(b−t, min r b)` / `t = min(b−q, min a b)`). The keystone
turning the layer-peel into the front-peel. -/
theorem twoVar_min_eq (a b r : ℕ) :
    (Finset.range (min a b + 1)).inf' (by simp) (fun t => (a - t) * (b - t) + t * r)
      = (Finset.range (min r b + 1)).inf' (by simp) (fun q => a * q + (b - q) * (r - q)) := by
  apply le_antisymm
  · -- LHS ≤ RHS: for each `q ≤ min r b`, bound `LHS` by the witness `t = min (b-q) (min a b)`.
    apply Finset.le_inf'
    intro q hq
    rw [Finset.mem_range, Nat.lt_succ_iff] at hq
    have hqr : q ≤ r := le_trans hq (min_le_left _ _)
    have hqb : q ≤ b := le_trans hq (min_le_right _ _)
    by_cases hc : b - q ≤ min a b
    · -- witness `t = b - q`: the summands coincide (`q = b - t` reflection).
      have hmem : (b - q) ∈ Finset.range (min a b + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]; exact hc
      refine le_trans (Finset.inf'_le _ hmem) (le_of_eq ?_)
      have h1 : b - q ≤ a := le_trans hc (min_le_left _ _)
      zify [h1, hqb, hqr, Nat.sub_le b q]
      ring
    · -- witness `t = min a b = a` (`a < b`); `(a-t) = 0`, reduce to `a·r ≤ a·q + (b-q)(r-q)`.
      push_neg at hc
      have hab : min a b = a := by
        rcases le_total a b with hle | hle
        · exact min_eq_left hle
        · exfalso; rw [min_eq_right hle] at hc; omega
      have hmem : (min a b) ∈ Finset.range (min a b + 1) := by
        rw [Finset.mem_range]; omega
      refine le_trans (Finset.inf'_le _ hmem) ?_
      rw [hab] at hc ⊢
      simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add]
      have haq : a ≤ b - q := by omega
      have e1 : a * r = a * q + a * (r - q) := by rw [← Nat.mul_add]; congr 1; omega
      rw [e1]; gcongr
  · -- RHS ≤ LHS: for each `t ≤ min a b`, bound `RHS` by the witness `q = min (b-t) (min r b)`.
    apply Finset.le_inf'
    intro t ht
    rw [Finset.mem_range, Nat.lt_succ_iff] at ht
    have hta : t ≤ a := le_trans ht (min_le_left _ _)
    have htb : t ≤ b := le_trans ht (min_le_right _ _)
    by_cases hc : b - t ≤ min r b
    · have hmem : (b - t) ∈ Finset.range (min r b + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]; exact hc
      refine le_trans (Finset.inf'_le _ hmem) (le_of_eq ?_)
      have hbr : b - t ≤ r := le_trans hc (min_le_left _ _)
      zify [hta, htb, hbr, Nat.sub_le b t]
      ring
    · push_neg at hc
      have hrb : min r b = r := by
        rcases le_total r b with hle | hle
        · exact min_eq_left hle
        · exfalso; rw [min_eq_right hle] at hc; omega
      have hmem : (min r b) ∈ Finset.range (min r b + 1) := by
        rw [Finset.mem_range]; omega
      refine le_trans (Finset.inf'_le _ hmem) ?_
      rw [hrb] at hc ⊢
      simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      have hrbt : r ≤ b - t := by omega
      have e1 : a * r = t * r + (a - t) * r := by rw [← Nat.add_mul]; congr 1; omega
      rw [e1, Nat.add_comm (t * r) ((a - t) * r)]
      gcongr

/-! ## The front-peel charge and its min -/

/-- The min of the tail widths `(M₁,…,M_{L+2})` of a `≥ 3`-width chain. -/
def tailMin (M : Fin (L + 1 + 1 + 1) → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (L + 1 + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => M i.succ)

/-- **The front-peel charge at tail-rank `q`** — `M₀·q + minAdm` of the tail chain `(M₁,…,M_{L+2})`
shifted down by `q`. The `q`-th candidate of the front-peel min. -/
def frontCharge (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) : ℕ :=
  M 0 * q + minAdm (fun i : Fin (L + 1 + 1) => M i.succ - q)

/-! ## Range bookkeeping helpers -/

/-- Shifting every width of a chain down by `q` shifts its min down by `q` (truncated subtraction
commutes with `inf'`, unconditionally). -/
theorem inf'_univ_sub_right {n : ℕ} (W : Fin (n + 1) → ℕ) (q : ℕ) :
    (Finset.univ : Finset (Fin (n + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => W i - q)
      = (Finset.univ : Finset (Fin (n + 1))).inf' ⟨0, Finset.mem_univ 0⟩ W - q := by
  apply le_antisymm
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (⟨0, Finset.mem_univ 0⟩) W
    rw [hi]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  · apply Finset.le_inf'
    intro i _
    exact Nat.sub_le_sub_right (Finset.inf'_le _ (Finset.mem_univ i)) q

/-- `q ≤ tailMin M` iff `q` is below every tail width `M₁,…,M_{L+2}`. -/
theorem le_tailMin_iff (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) :
    q ≤ tailMin M ↔ ∀ i : Fin (L + 1 + 1), q ≤ M i.succ := by
  rw [tailMin, Finset.le_inf'_iff]
  exact ⟨fun h i => h i (Finset.mem_univ i), fun h i _ => h i⟩

/-- The tail min splits off the head `M₁` from the deeper min `min(M₂,…,M_{L+2})`. -/
theorem tailMin_split (M : Fin (L + 1 + 1 + 1) → ℕ) :
    tailMin M = min (M 1)
      ((Finset.univ : Finset (Fin (L + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => M i.succ.succ)) := by
  set mW := (Finset.univ : Finset (Fin (L + 1))).inf' ⟨0, Finset.mem_univ 0⟩
    (fun i => M i.succ.succ) with hmW
  apply le_antisymm
  · refine le_min ?_ ?_
    · exact (le_tailMin_iff M (tailMin M)).mp le_rfl 0
    · rw [hmW]; apply Finset.le_inf'; intro i _
      exact (le_tailMin_iff M (tailMin M)).mp le_rfl i.succ
  · rw [le_tailMin_iff]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ j))

/-! ## The deliverables -/

/-- **The FRONT-PEEL identity `(FP)`.** `minAdm M` equals the min over tail-ranks `q ≤ tailMin M` of
the front-peel charge `M₀·q + minAdm ((M₁,…,M_L) − q)`. Arity induction: the LAYER-peel
(`sjChargeBudget_*`) expands `minAdm M`, the front-peel IH expands both reduced chains, and each
direction closes with a witness supplied by `twoVar_min_eq`. -/
theorem minAdm_eq_frontPeel (M : Fin (L + 1 + 1 + 1) → ℕ) :
    minAdm M = (Finset.range (tailMin M + 1)).inf'
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _)) (frontCharge M) := by
  induction L with
  | zero =>
    -- Base `n = 3`: `minAdm(M₀,M₁,M₂) = f = g = frontPeel`, the deep chain is the 2-width leaf.
    have htail : tailMin M = min (M 2) (M 1) := by
      rw [min_comm]
      apply le_antisymm
      · exact le_min ((le_tailMin_iff M _).mp le_rfl 0) ((le_tailMin_iff M _).mp le_rfl 1)
      · rw [le_tailMin_iff]; intro i; fin_cases i
        · exact min_le_left _ _
        · exact min_le_right _ _
    rw [← sjChargeBudget_recursion M]
    have hfe1 : (fun t => (M 0 - t) * (M 1 - t) + minAdm (redChain t M))
        = (fun t => (M 0 - t) * (M 1 - t) + t * M 2) := by
      funext t
      have h2 : minAdm (redChain t M) = t * M 2 := by
        rw [minAdm_two_eq, redChain_zero]; rfl
      rw [h2]
    rw [hfe1, twoVar_min_eq (M 0) (M 1) (M 2), htail]
    have hfe2 : (fun q => M 0 * q + (M 1 - q) * (M 2 - q)) = frontCharge M := by
      funext q
      have h2 : minAdm (fun i : Fin 2 => M i.succ - q) = (M 1 - q) * (M 2 - q) := by
        rw [minAdm_two_eq]; rfl
      rw [frontCharge, h2]
    rw [hfe2]
  | succ K IH =>
    -- Abbreviation: the deep tail-of-tail min `mW = min(M₂,…,M_{K+3})`.
    set mW := (Finset.univ : Finset (Fin (K + 1 + 1))).inf' ⟨0, Finset.mem_univ 0⟩
      (fun i => M i.succ.succ) with hmW
    have htail : tailMin M = min (M 1) mW := by rw [tailMin_split]
    -- IH expanded on the reduced chain `redChain t M`.
    have hIHred : ∀ (t : ℕ), minAdm (redChain t M)
        = (Finset.range (mW + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
            (fun ρ => t * ρ + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - ρ)) := by
      intro t
      have htm : tailMin (redChain t M) = mW := by
        have hfe : (fun i : Fin (K + 1 + 1) => (redChain t M) i.succ)
            = (fun i => M i.succ.succ) := by funext i; rw [redChain_succ]
        show (Finset.univ : Finset (Fin (K + 1 + 1))).inf' ⟨0, Finset.mem_univ 0⟩
            (fun i => (redChain t M) i.succ) = mW
        rw [hfe, hmW]
      have hfe2 : frontCharge (redChain t M)
          = (fun ρ => t * ρ + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - ρ)) := by
        funext ρ
        have hinner : (fun i : Fin (K + 1 + 1) => (redChain t M) i.succ - ρ)
            = (fun i => M i.succ.succ - ρ) := by funext i; rw [redChain_succ]
        rw [frontCharge, redChain_zero, hinner]
      rw [IH (redChain t M), htm, hfe2]
    -- IH expanded on the shifted tail chain `(M₁,…,M_{K+3}) − q`.
    have hIHsh : ∀ (q : ℕ), minAdm (fun i : Fin (K + 1 + 1 + 1) => M i.succ - q)
        = (Finset.range (mW - q + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
            (fun q'' => (M 1 - q) * q''
              + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - (q + q''))) := by
      intro q
      have htm : tailMin (fun i : Fin (K + 1 + 1 + 1) => M i.succ - q) = mW - q := by
        have hfe : (fun i : Fin (K + 1 + 1) => (fun j : Fin (K + 1 + 1 + 1) => M j.succ - q) i.succ)
            = (fun i => M i.succ.succ - q) := by funext i; rfl
        show (Finset.univ : Finset (Fin (K + 1 + 1))).inf' ⟨0, Finset.mem_univ 0⟩
            (fun i => (fun j : Fin (K + 1 + 1 + 1) => M j.succ - q) i.succ) = mW - q
        rw [hfe, hmW, inf'_univ_sub_right]
      have hfe2 : frontCharge (fun i : Fin (K + 1 + 1 + 1) => M i.succ - q)
          = (fun q'' => (M 1 - q) * q''
              + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - (q + q''))) := by
        funext q''
        simp only [frontCharge, Fin.succ_zero_eq_one', Nat.sub_sub]
      rw [IH (fun i : Fin (K + 1 + 1 + 1) => M i.succ - q), htm, hfe2]
    apply le_antisymm
    · -- `minAdm M ≤ frontPeel M`: per admissible `q`, witness via `twoVar`.
      apply Finset.le_inf'
      intro q hqmem
      rw [Finset.mem_range, Nat.lt_succ_iff] at hqmem
      have hqM1 : q ≤ M 1 := le_trans hqmem (by rw [htail]; exact min_le_left _ _)
      have hqmW : q ≤ mW := le_trans hqmem (by rw [htail]; exact min_le_right _ _)
      rw [frontCharge, hIHsh q]
      -- binding `q''`
      obtain ⟨q'', hq''mem, hq''eq⟩ := Finset.exists_mem_eq_inf'
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
        (fun q'' => (M 1 - q) * q'' + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - (q + q'')))
      rw [Finset.mem_range, Nat.lt_succ_iff] at hq''mem
      rw [hq''eq]
      set r := q + q'' with hr
      have hrmW : r ≤ mW := by omega
      have hqr : q ≤ r := by omega
      -- `f-inf' ≤ g-term(q)`, then descend the layer-peel + IH(red) at `ρ = r`.
      obtain ⟨t, htmem, hteq⟩ := Finset.exists_mem_eq_inf'
        (s := Finset.range (min (M 0) (M 1) + 1))
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
        (fun t => (M 0 - t) * (M 1 - t) + t * r)
      rw [Finset.mem_range, Nat.lt_succ_iff] at htmem
      have hfg : (M 0 - t) * (M 1 - t) + t * r ≤ M 0 * q + (M 1 - q) * (r - q) := by
        rw [← hteq, twoVar_min_eq (M 0) (M 1) r]
        refine Finset.inf'_le _ ?_
        rw [Finset.mem_range, Nat.lt_succ_iff]; exact le_min hqr hqM1
      have h1 := sjChargeBudget_le M t htmem
      have h2 : minAdm (redChain t M) ≤ t * r
          + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - r) := by
        rw [hIHred t]
        exact Finset.inf'_le _ (by rw [Finset.mem_range, Nat.lt_succ_iff]; exact hrmW)
      have hq'' : q'' = r - q := by omega
      rw [hq'']
      omega
    · -- `frontPeel M ≤ minAdm M`: pick the binding layer-peel cut + IH(red), witness `q'` via `twoVar`.
      obtain ⟨t, htmem, hteq⟩ := sjChargeBudget_binding M
      obtain ⟨ρ, hρmem, hρeq⟩ := Finset.exists_mem_eq_inf'
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
        (fun ρ => t * ρ + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - ρ))
      rw [Finset.mem_range, Nat.lt_succ_iff] at hρmem
      rw [hIHred t] at hteq
      rw [hρeq] at hteq
      set r := ρ with hrdef
      -- `g-inf' ≤ f-term(t)`; binding `q'` of `g`.
      obtain ⟨q', hq'mem, hq'eq⟩ := Finset.exists_mem_eq_inf'
        (s := Finset.range (min r (M 1) + 1))
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
        (fun q => M 0 * q + (M 1 - q) * (r - q))
      rw [Finset.mem_range, Nat.lt_succ_iff] at hq'mem
      have hq'r : q' ≤ r := le_trans hq'mem (min_le_left _ _)
      have hq'M1 : q' ≤ M 1 := le_trans hq'mem (min_le_right _ _)
      have hq'mW : q' ≤ mW := le_trans hq'r hρmem
      -- `frontPeel ≤ frontCharge M q'`
      have hq'tail : q' ∈ Finset.range (tailMin M + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff, htail]; exact le_min hq'M1 hq'mW
      refine le_trans (Finset.inf'_le _ hq'tail) ?_
      -- `frontCharge M q' ≤ M0 q' + (M1-q')(r-q') + D r`
      rw [frontCharge, hIHsh q']
      have hsh : (Finset.range (mW - q' + 1)).inf'
            (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
            (fun q'' => (M 1 - q') * q''
              + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - (q' + q'')))
          ≤ (M 1 - q') * (r - q')
              + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - r) := by
        have hmem : (r - q') ∈ Finset.range (mW - q' + 1) := by
          rw [Finset.mem_range, Nat.lt_succ_iff]; omega
        refine le_trans (Finset.inf'_le _ hmem) ?_
        show (M 1 - q') * (r - q')
            + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - (q' + (r - q')))
          ≤ (M 1 - q') * (r - q') + minAdm (fun i : Fin (K + 1 + 1) => M i.succ.succ - r)
        rw [show q' + (r - q') = r from by omega]
      -- `f-inf' ≤ f-term(t)`, `f-inf' = g-inf'`, `g-inf' = g-term(q')`
      have hgf : M 0 * q' + (M 1 - q') * (r - q')
          ≤ (M 0 - t) * (M 1 - t) + t * r := by
        rw [← hq'eq, ← twoVar_min_eq (M 0) (M 1) r]
        exact Finset.inf'_le _ (by rw [Finset.mem_range, Nat.lt_succ_iff]; exact htmem)
      -- assemble: minAdm M = f-term(t) + D r ≥ g-term(q') + D r ≥ frontCharge M q'
      rw [← hteq]
      omega

/-- **The front-peel inequality.** At every admissible tail-rank `q ≤ tailMin M`, the front-peel
charge dominates the codim: `minAdm M ≤ M₀·q + minAdm ((M₁,…,M_L) − q)`. A term of the achieved
`minAdm_eq_frontPeel` min. -/
theorem frontCharge_ge_minAdm (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M) :
    minAdm M ≤ frontCharge M q := by
  rw [minAdm_eq_frontPeel M]
  exact Finset.inf'_le _ (by rw [Finset.mem_range, Nat.lt_succ_iff]; exact hq)

/-! ## Fidelity anchors (cert §C worked examples) -/

-- `(3,3,3,4)`: `tailMin = 3`, `frontCharge` over `q = 0..3` is `8,7,7,9`, min `= 7 = minAdm`.
example : tailMin (![3, 3, 3, 4] : Fin 4 → ℕ) = 3 := by decide
example : minAdm (![3, 3, 3, 4] : Fin 4 → ℕ) = 7 := by decide
example : frontCharge (![3, 3, 3, 4] : Fin 4 → ℕ) 2 = 7 := by decide
example : frontCharge (![3, 3, 3, 4] : Fin 4 → ℕ) 3 = 9 := by decide

-- `(4,4,2)`: the top component sits at the SUB-generic tail rank `q = 1` (`< tailMin = 2`),
-- `frontCharge 1 = 7 = minAdm` while `frontCharge 0 = frontCharge 2 = 8`.
example : minAdm (![4, 4, 2] : Fin 3 → ℕ) = 7 := by decide
example : frontCharge (![4, 4, 2] : Fin 3 → ℕ) 1 = 7 := by decide
example : frontCharge (![4, 4, 2] : Fin 3 → ℕ) 0 = 8 := by decide

end DLNFibre.DLN.RLCT

