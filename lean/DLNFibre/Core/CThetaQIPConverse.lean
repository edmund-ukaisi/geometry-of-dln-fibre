import DLNFibre.Core.CThetaQIP

/-!
# `DLNFibre.Core.CThetaQIPConverse` — the QIP converse (Thm 6.1, `≥`), closing to equality

The HARD half of Lehalleur–Rimányi Theorem 6.1: for a **weakly-increasing** `d`, every
`codimForm`-minimiser over `kostantPartitions d 0` is **horizontal-lace** (HL), hence lies in the
`mOfE`-image, hence has `codimForm` value `≥ qipMin d`. With the committed easy `≤`
(`Core.CThetaQIP.cCodim_le_qipMin`) this closes the QIP to equality `cCodim d 0 = qipMin d`.

**Strategy — single-step contradiction (NOT a descent measure).** Prototyping falsified the descent
measure `∑ m·min(a, N−b)`; the converse is proved by: a non-HL KP admits *one* strictly-`codimForm`-
decreasing valid corner-`0` move (a **concat** `[a,b]+[b+1,d']→[a,d']`), so a minimiser is HL.

**The exhaustiveness mechanism (form-level, no geometry).** An interior interval `[a,b]`
(`1 ≤ a, b ≤ N-1`, `m(a,b) > 0`) always has a right partner: the Kostant constraints at adjacent
vertices `b, b+1` give `d_b + Starts_b = d_{b+1} + Ends_b` (`Starts_b` = intervals from `b+1`,
`Ends_b` = intervals ending at `b`); `Monotone d` (`d_b ≤ d_{b+1}`) forces `Ends_b ≤ Starts_b`, and
`m(a,b) > 0` makes `Ends_b > 0`, so `Starts_b > 0`: some `m(b+1, d') > 0`. The concat then strictly
drops `codimForm`. **`Monotone d` is the ONLY hypothesis** — `d 0 ≥ 1` is *not* needed: the argument
routes through the edge `b|b+1`, never column `a-1`. (The `d=(1,0,1,0)` "walled" obstruction is
*non-monotone*; for monotone `d`, `cCodim = qipMin` holds even at `d 0 = 0`, verified N≤4.)

**Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## Horizontal-lace partitions

A partition `m` is **horizontal-lace** when every supported interval touches an end (`m (a,b)=0`
for every *interior* interval `1 ≤ a`, `b ≤ N-1`); equivalently, only `[0,t]`/`[s,N]` carry mass.
For weakly-increasing `d` (corner `0`) these are exactly the `mOfE`-image (`mOfE_surj_of_hl`). -/

/-- `m` is **horizontal-lace**: it vanishes on every interior interval (`1 ≤ a ∧ b ≤ N - 1`). -/
def IsHL (m : Fin (N + 1) × Fin (N + 1) → ℕ) : Prop :=
  ∀ p : Fin (N + 1) × Fin (N + 1), 1 ≤ (p.1 : ℕ) → (p.2 : ℕ) ≤ N - 1 → m p = 0

instance (m : Fin (N + 1) × Fin (N + 1) → ℕ) : Decidable (IsHL m) := by unfold IsHL; infer_instance

/-! ## The `codimForm` bilinear form and its expansion

`codimBil A B` is `codimForm`'s sum with the two factors split: `codimForm M = codimBil M M`
(`codimBil_self`). It is bi-additive, giving `codimForm (A+B) = codimForm A + codimBil A B
+ codimBil B A + codimForm B` (`codimForm_add`). A move changes the array at a few points, turning
the `codimForm` difference into a finite sum the Δ-lemma collapses. -/

/-- The bilinear form underlying `codimForm`: `∑_{1≤i≤u≤j≤v≤N} A (i-1) (j-1) · B u v`. -/
def codimBil (N : ℕ) (A B : ℤ → ℤ → ℤ) : ℤ :=
  ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
    ∑ v ∈ Finset.Icc j (N : ℤ),
      A (i - 1) (j - 1) * B u v

/-- `codimForm M = codimBil M M`. -/
theorem codimBil_self (M : ℤ → ℤ → ℤ) : codimBil N M M = codimForm N M := rfl

/-- `codimBil` is additive in its first argument. -/
theorem codimBil_add_left (A A' B : ℤ → ℤ → ℤ) :
    codimBil N (A + A') B = codimBil N A B + codimBil N A' B := by
  unfold codimBil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ ↦ ?_)
  simp only [Pi.add_apply]; ring

/-- `codimBil` is additive in its second argument. -/
theorem codimBil_add_right (A B B' : ℤ → ℤ → ℤ) :
    codimBil N A (B + B') = codimBil N A B + codimBil N A B' := by
  unfold codimBil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ ↦ ?_)
  simp only [Pi.add_apply]; ring

/-- `codimBil` is subtractive in its second argument. -/
theorem codimBil_sub_right (A B B' : ℤ → ℤ → ℤ) :
    codimBil N A (B - B') = codimBil N A B - codimBil N A B' := by
  have h := codimBil_add_right (N := N) A (B - B') B'
  rw [sub_add_cancel] at h; rw [h]; ring

/-- `codimBil` is subtractive in its first argument. -/
theorem codimBil_sub_left (A A' B : ℤ → ℤ → ℤ) :
    codimBil N (A - A') B = codimBil N A B - codimBil N A' B := by
  have h := codimBil_add_left (N := N) (A - A') A' B
  rw [sub_add_cancel] at h; rw [h]; ring

/-- **`codimForm` expansion.** `codimForm (A + B) = codimForm A + codimBil A B + codimBil B A
+ codimForm B`. -/
theorem codimForm_add (A B : ℤ → ℤ → ℤ) :
    codimForm N (A + B) = codimForm N A + codimBil N A B + codimBil N B A + codimForm N B := by
  rw [← codimBil_self, codimBil_add_left, codimBil_add_right, codimBil_add_right,
    codimBil_self, codimBil_self]
  ring

/-! ## The concat move `[a,b] + [c,d'] → [a,d']` (with `c = b+1`)

`concatMove m a b c d'` merges `[a,b]` (ending at `b`) and `[c,d']` (starting at `c = b+1`) into
`[a,d']`. With `a ≤ b`, `c = b+1`, `c ≤ d'`, `a ≥ 1` (so `[a,d'] ≠ [0,N]`), both sources present, it
is a valid corner-`0` Kostant partition of the same `d` (three changed entries at distinct keys, no
underflow), and `codimForm` strictly drops. The vertices are `Fin (N+1)`; `c = b+1` is carried as a
hypothesis (`(c : ℕ) = b + 1`) so the move definition stays `Fin`-arithmetic-free. -/

/-- The concat move on the multiplicity array: `m(a,b) −= 1`, `m(c,d') −= 1`, `m(a,d') += 1`. -/
def concatMove (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b c d' : Fin (N + 1)) :
    Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ m p + (if p = (a, d') then 1 else 0)
    - (if p = (a, b) then 1 else 0) - (if p = (c, d') then 1 else 0)

/-- The ℤ-delta of the concat move: `+1` at `(a,d')`, `−1` at `(a,b)`, `−1` at `(c,d')`. -/
def concatDelta (a b c d' : Fin (N + 1)) : ℤ → ℤ → ℤ :=
  fun α β ↦ (if α = (a : ℤ) ∧ β = (d' : ℤ) then 1 else 0)
    - (if α = (a : ℤ) ∧ β = (b : ℤ) then 1 else 0)
    - (if α = (c : ℤ) ∧ β = (d' : ℤ) then 1 else 0)

/-- **The `extendℤ`/delta connection.** Under the move's preconditions (`a ≤ b`, `b < c`, `c ≤ d'`,
`1 ≤ a`, sources present), `extendℤ (concatMove m a b c d') = extendℤ m + concatDelta a b c d'`.
The three changed keys are distinct, so at each point at most one indicator fires and subtraction
is honest. -/
theorem extendℤ_concatMove {m : Fin (N + 1) × Fin (N + 1) → ℕ} {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (b : ℕ) < c) (hcd : (c : ℕ) ≤ d')
    (hsab : 1 ≤ m (a, b)) (hscd : 1 ≤ m (c, d')) :
    extendℤ (concatMove m a b c d') = extendℤ m + concatDelta a b c d' := by
  -- the three changed keys are pairwise distinct
  have hbd : (b : ℕ) ≠ d' := by omega
  have hac : (a : ℕ) ≠ c := by omega
  funext α β
  simp only [Pi.add_apply, extendℤ, concatDelta]
  by_cases hbox : (0 : ℤ) ≤ α ∧ α ≤ β ∧ β ≤ (N : ℤ)
  · rw [dif_pos hbox, dif_pos hbox]
    -- in box: compare `concatMove` value (ℕ, cast) with `m` value + ℤ-delta
    obtain ⟨hα0, hαβ, hβN⟩ := hbox
    set q : Fin (N + 1) × Fin (N + 1) := (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) with hq
    -- key equalities: `q = (a, d')` etc. translate to the ℤ index conditions
    have eAD : (q = (a, d')) ↔ (α = (a : ℤ) ∧ β = (d' : ℤ)) := by
      rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
    have eAB : (q = (a, b)) ↔ (α = (a : ℤ) ∧ β = (b : ℤ)) := by
      rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
    have eCD : (q = (c, d')) ↔ (α = (c : ℤ) ∧ β = (d' : ℤ)) := by
      rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
    rw [show concatMove m a b c d' (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩)
        = concatMove m a b c d' q from rfl, concatMove]
    -- distinctness: at most one of the three keys equals `q`; rewrite the Fin-key ifs (concatMove)
    -- and the ℤ-cond ifs (concatDelta, via eAD/eAB/eCD) together per case.
    have hdb' : d' ≠ b := fun h ↦ hbd (by rw [h])
    have hac' : a ≠ c := fun h ↦ hac (by rw [h])
    by_cases h1 : q = (a, d')
    · have h2 : q ≠ (a, b) := by
        rw [h1]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun _ ↦ hdb'
      have h3 : q ≠ (c, d') := by
        rw [h1]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun h ↦ absurd h hac'
      rw [if_pos h1, if_neg h2, if_neg h3, if_pos (eAD.mp h1),
        if_neg (fun h ↦ h2 (eAB.mpr h)), if_neg (fun h ↦ h3 (eCD.mpr h))]
      push_cast; ring
    · by_cases h2 : q = (a, b)
      · have h3 : q ≠ (c, d') := by
          rw [h2]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun _ ↦ fun h ↦ hdb' h.symm
        rw [if_neg h1, if_pos h2, if_neg h3, if_neg (fun h ↦ h1 (eAD.mpr h)),
          if_pos (eAB.mp h2), if_neg (fun h ↦ h3 (eCD.mpr h))]
        have hpos : 1 ≤ m q := by rw [h2]; exact hsab
        push_cast; omega
      · by_cases h3 : q = (c, d')
        · rw [if_neg h1, if_neg h2, if_pos h3, if_neg (fun h ↦ h1 (eAD.mpr h)),
            if_neg (fun h ↦ h2 (eAB.mpr h)), if_pos (eCD.mp h3)]
          have hpos : 1 ≤ m q := by rw [h3]; exact hscd
          push_cast; omega
        · rw [if_neg h1, if_neg h2, if_neg h3, if_neg (fun h ↦ h1 (eAD.mpr h)),
            if_neg (fun h ↦ h2 (eAB.mpr h)), if_neg (fun h ↦ h3 (eCD.mpr h))]
          simp
  · -- out of box: all three ℤ-indicators vanish (their keys are in box)
    simp only [dif_neg hbox]
    have haN : (a : ℤ) ≤ N := by have := a.isLt; omega
    have hdN : (d' : ℤ) ≤ N := by have := d'.isLt; omega
    have had : (a : ℤ) ≤ d' := by omega
    have hab' : (a : ℤ) ≤ b := by omega
    have hcdN : (c : ℤ) ≤ d' := by omega
    rw [if_neg (by rintro ⟨h1, h2⟩; exact hbox ⟨by omega, by omega, by omega⟩),
      if_neg (by rintro ⟨h1, h2⟩; exact hbox ⟨by omega, by omega, by omega⟩),
      if_neg (by rintro ⟨h1, h2⟩; exact hbox ⟨by omega, by omega, by omega⟩)]
    ring

/-! ### The strict `codimForm` decrease of the concat move

`extendℤ (concatMove …) = extendℤ m + δ` (`extendℤ_concatMove`), so by `codimForm_add` the change is
`codimBil M δ + codimBil δ M + codimForm δ`. Each correction collapses (δ supported at 3 points):
the two bilinear terms are negated **rectangles** `∑_{[a+1,c]×[c,d']} M`, `codimForm δ = 1`; each
rectangle dominates a source (`M(a,b)` resp. `M(c,d')`), both `≥ 1`, so the change is `≤ -1`. -/

/-- `extendℤ m` at `Fin`-points `(a,b)` with `a ≤ b`: drops the guard, gives `m (a,b)`. -/
theorem extendℤ_fin_eq (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b : Fin (N + 1)} (hab : a ≤ b) :
    extendℤ m (a : ℤ) (b : ℤ) = (m (a, b) : ℤ) := by
  rw [extendℤ_in_box m (by positivity) (by exact_mod_cast hab) (by have := b.isLt; omega)]
  have ha : (⟨(a : ℤ).toNat, by have := a.isLt; omega⟩ : Fin (N + 1)) = a := Fin.ext (by simp)
  have hb : (⟨(b : ℤ).toNat, by have := b.isLt; omega⟩ : Fin (N + 1)) = b := Fin.ext (by simp)
  rw [ha, hb]

/-- `extendℤ m` is entrywise nonnegative (it is a cast ℕ-array, else `0`). -/
theorem extendℤ_nonneg (m : Fin (N + 1) × Fin (N + 1) → ℕ) (α β : ℤ) : 0 ≤ extendℤ m α β := by
  unfold extendℤ; split_ifs with h
  · exact Int.natCast_nonneg _
  · exact le_refl _

/-- **Single-point right-slot collapse.** For a point `(p, q)` with `1 ≤ p ≤ q ≤ N`,
`codimBil M (indicator at (p,q)) = ∑_{i ∈ [1,p]} ∑_{j ∈ [p,q]} M (i-1) (j-1)`. The second-slot
indicator collapses `u → p`, `v → q`; surviving `i`-range is `i ≤ p`, the `j`-range is `[p, q]`. -/
theorem codimBil_single_right (M : ℤ → ℤ → ℤ) {p q : ℤ} (_hp : 1 ≤ p) (hpq : p ≤ q)
    (hq : q ≤ (N : ℤ)) :
    codimBil N M (fun α β ↦ if α = p ∧ β = q then (1 : ℤ) else 0)
      = ∑ i ∈ Finset.Icc (1 : ℤ) p, ∑ j ∈ Finset.Icc p q, M (i - 1) (j - 1) := by
  unfold codimBil
  -- collapse `u → p` and `v → q` (only nonzero indicator), per the (i,u,j,v) nesting
  have step : ∀ i ∈ Finset.Icc (1 : ℤ) N,
      (∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ), ∑ v ∈ Finset.Icc j (N : ℤ),
        M (i - 1) (j - 1) * (if u = p ∧ v = q then (1 : ℤ) else 0))
        = if i ≤ p then ∑ j ∈ Finset.Icc p q, M (i - 1) (j - 1) else 0 := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    by_cases hip : i ≤ p
    · rw [if_pos hip, Finset.sum_eq_single_of_mem p (by simp only [Finset.mem_Icc]; omega)]
      · -- now collapse the inner `j`-sum over `[p,N]`: the `v→q` step kills `j > q`
        have hjstep : ∀ j ∈ Finset.Icc p (N : ℤ),
            (∑ v ∈ Finset.Icc j (N : ℤ), M (i - 1) (j - 1) * (if p = p ∧ v = q then (1 : ℤ) else 0))
              = if j ≤ q then M (i - 1) (j - 1) else 0 := by
          intro j hj; simp only [Finset.mem_Icc] at hj
          by_cases hjq : j ≤ q
          · rw [if_pos hjq, Finset.sum_eq_single_of_mem q (by simp only [Finset.mem_Icc]; omega)]
            · simp
            · intro v _ hvq; rw [if_neg (by rintro ⟨-, h⟩; exact hvq h), mul_zero]
          · rw [if_neg hjq]
            refine Finset.sum_eq_zero (fun v hv ↦ ?_)
            simp only [Finset.mem_Icc] at hv
            rw [if_neg (by rintro ⟨-, h⟩; omega), mul_zero]
        rw [Finset.sum_congr rfl hjstep, ← Finset.sum_filter]
        congr 1
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      · intro u _ hup
        refine Finset.sum_eq_zero (fun j _ ↦ Finset.sum_eq_zero (fun v _ ↦ ?_))
        rw [if_neg (by rintro ⟨h, -⟩; exact hup h), mul_zero]
    · rw [if_neg hip]
      refine Finset.sum_eq_zero (fun u hu ↦ Finset.sum_eq_zero (fun j _ ↦
        Finset.sum_eq_zero (fun v _ ↦ ?_)))
      simp only [Finset.mem_Icc] at hu
      rw [if_neg (by rintro ⟨h, -⟩; omega), mul_zero]
  rw [Finset.sum_congr rfl step, ← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

/-- **Right-slot collapse.** `codimBil M δ` is the negated rectangle `∑_{[a+1,c]×[c,d']} M(i-1,j-1)`
(δ in the second slot; only the three `Q` keys survive, leaving the rectangle). -/
theorem codimBil_concatDelta_right (M : ℤ → ℤ → ℤ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 1) (hcd : (c : ℕ) ≤ d') (ha1 : 1 ≤ (a : ℕ)) :
    codimBil N M (concatDelta a b c d')
      = - ∑ i ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ),
          M (i - 1) (j - 1) := by
  -- `concatDelta = single(a,d') - single(a,b) - single(c,d')`; single-point collapse on each.
  have hsplit : concatDelta a b c d'
      = (fun α β ↦ if α = (a : ℤ) ∧ β = (d' : ℤ) then (1 : ℤ) else 0)
        - (fun α β ↦ if α = (a : ℤ) ∧ β = (b : ℤ) then (1 : ℤ) else 0)
        - (fun α β ↦ if α = (c : ℤ) ∧ β = (d' : ℤ) then (1 : ℤ) else 0) := rfl
  -- bounds for the three points
  have hAd : 1 ≤ (a : ℤ) ∧ (a : ℤ) ≤ d' ∧ (d' : ℤ) ≤ N := by
    have := d'.isLt
    exact ⟨by exact_mod_cast ha1, by exact_mod_cast (by omega : (a:ℕ) ≤ d'), by omega⟩
  have hAb : 1 ≤ (a : ℤ) ∧ (a : ℤ) ≤ b ∧ (b : ℤ) ≤ N := by
    have := b.isLt; exact ⟨by exact_mod_cast ha1, by exact_mod_cast hab, by omega⟩
  have hCd : 1 ≤ (c : ℤ) ∧ (c : ℤ) ≤ d' ∧ (d' : ℤ) ≤ N := by
    have := d'.isLt
    exact ⟨by exact_mod_cast (by omega : 1 ≤ (c:ℕ)), by exact_mod_cast hcd, by omega⟩
  rw [hsplit, codimBil_sub_right, codimBil_sub_right,
    codimBil_single_right M hAd.1 hAd.2.1 hAd.2.2,
    codimBil_single_right M hAb.1 hAb.2.1 hAb.2.2,
    codimBil_single_right M hCd.1 hCd.2.1 hCd.2.2]
  -- telescoping: T(a,d') − T(a,b) − T(c,d') = −∑_{[a+1,c]×[c,d']} M(i-1)(j-1).
  -- (1) `Icc a d' = Icc a b ⊎ Icc c d'` at the `j`-level: T(a,d') − T(a,b) = ∑_{[1,a]}∑_{[c,d']}.
  have hjsplit : ∀ i : ℤ, (∑ j ∈ Finset.Icc (a : ℤ) (d' : ℤ), M (i - 1) (j - 1))
      = (∑ j ∈ Finset.Icc (a : ℤ) (b : ℤ), M (i - 1) (j - 1))
        + ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ), M (i - 1) (j - 1) := by
    intro i; rw [← Finset.sum_union]
    · congr 1; ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    · rw [Finset.disjoint_left]; intro x hx hx2; simp only [Finset.mem_Icc] at hx hx2; omega
  have hT1 :
      (∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ), ∑ j ∈ Finset.Icc (a : ℤ) (d' : ℤ), M (i - 1) (j - 1))
      - ∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ), ∑ j ∈ Finset.Icc (a : ℤ) (b : ℤ), M (i - 1) (j - 1)
      = ∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ), ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ), M (i - 1) (j - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_); rw [hjsplit i]; ring
  -- (2) `Icc 1 c = Icc 1 a ⊎ Icc (a+1) c` at the `i`-level: T(c,d') = ∑_{[1,a]}∑_{[c,d']} + rect.
  have hisplit :
      (∑ i ∈ Finset.Icc (1 : ℤ) (c : ℤ), ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ), M (i - 1) (j - 1))
      = (∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ), ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ), M (i - 1) (j - 1))
        + ∑ i ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ),
            M (i - 1) (j - 1) := by
    rw [← Finset.sum_union]
    · congr 1; ext i; simp only [Finset.mem_Icc, Finset.mem_union]
      have : (a : ℤ) + 1 ≤ (c : ℤ) := by
        exact_mod_cast (by omega : (a : ℕ) + 1 ≤ c)
      omega
    · rw [Finset.disjoint_left]; intro x hx hx2; simp only [Finset.mem_Icc] at hx hx2; omega
  rw [hisplit]; linarith [hT1]

/-- **Single-point left-slot collapse.** For a point `(p, q)` with `0 ≤ p ≤ q ≤ N`,
`codimBil (indicator at (p,q)) M = ∑_{u ∈ [p+1,q+1]} ∑_{v ∈ [q+1,N]} M u v`. The first-slot ind.
collapses `i → p+1`, `j → q+1`; surviving `u`-range is `[p+1, q+1]`, the `v`-range is `[q+1, N]`. -/
theorem codimBil_single_left (M : ℤ → ℤ → ℤ) {p q : ℤ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hq : q ≤ (N : ℤ)) :
    codimBil N (fun α β ↦ if α = p ∧ β = q then (1 : ℤ) else 0) M
      = ∑ u ∈ Finset.Icc (p + 1) (q + 1), ∑ v ∈ Finset.Icc (q + 1) (N : ℤ), M u v := by
  unfold codimBil
  -- when `q + 1 > N` (`q = N`): the inner `j = q+1` is out of range, both sides are `0`.
  by_cases hqN : q + 1 ≤ (N : ℤ)
  swap
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro u hu; simp only [Finset.mem_Icc] at hu
      apply Finset.sum_eq_zero; intro v hv; simp only [Finset.mem_Icc] at hv; omega
    · intro i _
      refine Finset.sum_eq_zero (fun u _ ↦ Finset.sum_eq_zero (fun j hj ↦
        Finset.sum_eq_zero (fun v _ ↦ ?_)))
      simp only [Finset.mem_Icc] at hj
      exact mul_eq_zero_of_left (if_neg (by rintro ⟨-, h⟩; omega)) _
  -- collapse outer `i → p+1` (the only `i` with `i-1=p` in the range, if `p+1 ≤ N`)
  by_cases hpN : p + 1 ≤ (N : ℤ)
  · rw [Finset.sum_eq_single_of_mem (p + 1) (by simp only [Finset.mem_Icc]; omega)]
    · -- inner: `∑_{u∈[p+1,N]}∑_{j∈[u,N]}∑_{v∈[j,N]} [p=p ∧ j-1=q] M u v`
      -- collapse `j → q+1` (needs `q+1∈[u,N]`); then `v`-range is `[q+1,N]`, `u`-range `[p+1,q+1]`
      have hu : ∀ u ∈ Finset.Icc (p + 1) (N : ℤ),
          (∑ j ∈ Finset.Icc u (N : ℤ), ∑ v ∈ Finset.Icc j (N : ℤ),
            (if (p + 1) - 1 = p ∧ j - 1 = q then (1 : ℤ) else 0) * M u v)
            = if u ≤ q + 1 then ∑ v ∈ Finset.Icc (q + 1) (N : ℤ), M u v else 0 := by
        intro u hu; simp only [Finset.mem_Icc] at hu
        by_cases huq : u ≤ q + 1
        · rw [if_pos huq,
            Finset.sum_eq_single_of_mem (q + 1) (by simp only [Finset.mem_Icc]; omega)]
          · refine Finset.sum_congr rfl (fun v _ ↦ ?_); rw [if_pos ⟨by ring, by ring⟩, one_mul]
          · intro j _ hjq
            refine Finset.sum_eq_zero (fun v _ ↦ ?_)
            rw [if_neg (by rintro ⟨-, h⟩; exact hjq (by omega)), zero_mul]
        · rw [if_neg huq]
          refine Finset.sum_eq_zero (fun j hj ↦ Finset.sum_eq_zero (fun v _ ↦ ?_))
          simp only [Finset.mem_Icc] at hj
          rw [if_neg (by rintro ⟨-, h⟩; omega), zero_mul]
      rw [Finset.sum_congr rfl hu, ← Finset.sum_filter]
      congr 1; ext u; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    · intro i hi hip
      refine Finset.sum_eq_zero (fun u _ ↦ Finset.sum_eq_zero (fun j _ ↦
        Finset.sum_eq_zero (fun v _ ↦ ?_)))
      exact mul_eq_zero_of_left (if_neg (by rintro ⟨h, -⟩; exact hip (by omega))) _
  · -- `p + 1 > N` is impossible: `hqN : q+1 ≤ N` and `p ≤ q` give `p+1 ≤ N`.
    exact absurd hqN (by omega)

/-- **Left-slot collapse.** `codimBil δ M` is the negated rectangle `∑_{[a+1,c]×[c,d']} M u v`. -/
theorem codimBil_concatDelta_left (M : ℤ → ℤ → ℤ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 1) (hcd : (c : ℕ) ≤ d') (ha1 : 1 ≤ (a : ℕ)) :
    codimBil N (concatDelta a b c d') M
      = - ∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ),
          M u v := by
  have hsplit : concatDelta a b c d'
      = (fun α β ↦ if α = (a : ℤ) ∧ β = (d' : ℤ) then (1 : ℤ) else 0)
        - (fun α β ↦ if α = (a : ℤ) ∧ β = (b : ℤ) then (1 : ℤ) else 0)
        - (fun α β ↦ if α = (c : ℤ) ∧ β = (d' : ℤ) then (1 : ℤ) else 0) := rfl
  have hAd : 0 ≤ (a : ℤ) ∧ (a : ℤ) ≤ d' ∧ (d' : ℤ) ≤ N := by
    have := d'.isLt; exact ⟨by positivity, by exact_mod_cast (by omega : (a:ℕ) ≤ d'), by omega⟩
  have hAb : 0 ≤ (a : ℤ) ∧ (a : ℤ) ≤ b ∧ (b : ℤ) ≤ N := by
    have := b.isLt; exact ⟨by positivity, by exact_mod_cast hab, by omega⟩
  have hCd : 0 ≤ (c : ℤ) ∧ (c : ℤ) ≤ d' ∧ (d' : ℤ) ≤ N := by
    have := d'.isLt; exact ⟨by positivity, by exact_mod_cast hcd, by omega⟩
  rw [hsplit, codimBil_sub_left, codimBil_sub_left,
    codimBil_single_left M hAd.1 hAd.2.1 hAd.2.2,
    codimBil_single_left M hAb.1 hAb.2.1 hAb.2.2,
    codimBil_single_left M hCd.1 hCd.2.1 hCd.2.2]
  -- telescoping on `M u v`: S(a,d') − S(a,b) − S(c,d') = −∑_{[a+1,c]×[c,d']} M u v,
  -- where S(p,q) = ∑_{u∈[p+1,q+1]}∑_{v∈[q+1,N]} M u v.
  have hb1 : (b : ℤ) + 1 = (c : ℤ) := by push_cast [hbc]; ring
  have hac1 : (a : ℤ) + 1 ≤ (c : ℤ) := by exact_mod_cast (by omega : (a : ℕ) + 1 ≤ c)
  have hcd1 : (c : ℤ) ≤ (d' : ℤ) := by exact_mod_cast hcd
  rw [hb1]
  -- u-split for S(a,d'): `Icc (a+1) (d'+1) = Icc (a+1) c ⊎ Icc (c+1) (d'+1)`
  have husplit :
      (∑ u ∈ Finset.Icc ((a : ℤ) + 1) ((d' : ℤ) + 1), ∑ v ∈ Finset.Icc ((d' : ℤ) + 1) (N : ℤ),
          M u v)
      = (∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc ((d' : ℤ) + 1) (N : ℤ), M u v)
        + ∑ u ∈ Finset.Icc ((c : ℤ) + 1) ((d' : ℤ) + 1), ∑ v ∈ Finset.Icc ((d' : ℤ) + 1) (N : ℤ),
            M u v := by
    rw [← Finset.sum_union]
    · congr 1; ext u; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    · rw [Finset.disjoint_left]; intro x hx hx2; simp only [Finset.mem_Icc] at hx hx2; omega
  -- v-split for the `c`-row: `Icc c N = Icc c d' ⊎ Icc (d'+1) N`
  have hvsplit : ∀ u : ℤ, (∑ v ∈ Finset.Icc (c : ℤ) (N : ℤ), M u v)
      = (∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ), M u v)
        + ∑ v ∈ Finset.Icc ((d' : ℤ) + 1) (N : ℤ), M u v := by
    intro u; rw [← Finset.sum_union]
    · congr 1; ext v; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    · rw [Finset.disjoint_left]; intro x hx hx2; simp only [Finset.mem_Icc] at hx hx2; omega
  rw [husplit]
  -- the `S(a,b)`-row is over `Icc (a+1) c × Icc c N`; split its `v` via `hvsplit`
  have hSab : (∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc (c : ℤ) (N : ℤ), M u v)
      = (∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ), M u v)
        + ∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc ((d' : ℤ) + 1) (N : ℤ),
            M u v := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun u _ ↦ hvsplit u)
  rw [hSab]; ring

/-- **Self term.** `codimForm (concatDelta …) = 1`. -/
theorem codimForm_concatDelta {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 1) (hcd : (c : ℕ) ≤ d') (ha1 : 1 ≤ (a : ℕ)) :
    codimForm N (concatDelta a b c d') = 1 := by
  -- `codimForm δ = codimBil δ δ`; the left-collapse rectangle of `δ` is `−1` (only `(c,d')`).
  rw [← codimBil_self, codimBil_concatDelta_left _ hab hbc hcd ha1]
  -- evaluate `∑_{u∈[a+1,c]}∑_{v∈[c,d']} δ(u)(v)`: only `(u,v)=(c,d')` survives, giving `−1`.
  have hac1 : (a : ℤ) + 1 ≤ (c : ℤ) := by exact_mod_cast (by omega : (a : ℕ) + 1 ≤ c)
  have hcd1 : (c : ℤ) ≤ (d' : ℤ) := by exact_mod_cast hcd
  have hca : (c : ℤ) ≠ (a : ℤ) := by
    have : (a : ℕ) ≠ c := by omega
    exact fun h ↦ this (by exact_mod_cast h.symm)
  rw [show (∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ),
        concatDelta a b c d' u v) = -1 from ?_]
  · ring
  -- the rectangle sum of `δ`
  rw [Finset.sum_eq_single_of_mem (c : ℤ) (by simp only [Finset.mem_Icc]; omega)]
  · rw [Finset.sum_eq_single_of_mem (d' : ℤ) (by simp only [Finset.mem_Icc]; omega)]
    · -- `δ(c,d') = [c=a∧d'=d'] − [c=a∧d'=b] − [c=c∧d'=d'] = 0 − 0 − 1 = −1`
      unfold concatDelta
      rw [if_neg (by rintro ⟨h, -⟩; exact hca h), if_neg (by rintro ⟨h, -⟩; exact hca h),
        if_pos ⟨rfl, rfl⟩]; ring
    · intro v _ hvd'
      unfold concatDelta
      rw [if_neg (by rintro ⟨h, -⟩; exact hca h), if_neg (by rintro ⟨h, -⟩; exact hca h),
        if_neg (by rintro ⟨-, h⟩; exact hvd' h)]; ring
  · intro u hu huc
    -- for `u ≠ c` in `[a+1,c]`, `u < c`; `δ(u,v) = 0` (all keys need `u ∈ {a,c}`, but `u > a`)
    refine Finset.sum_eq_zero (fun v _ ↦ ?_)
    simp only [Finset.mem_Icc] at hu
    have hua : (u : ℤ) ≠ (a : ℤ) := by omega
    unfold concatDelta
    rw [if_neg (by rintro ⟨h, -⟩; exact hua h), if_neg (by rintro ⟨h, -⟩; exact hua h),
      if_neg (by rintro ⟨h, -⟩; exact huc h)]; ring

/-- **The concat move strictly drops `codimForm` (by ≥ 1).** With both sources present, rectangles
each dominate a source entry (`≥ 1`), so the total change `−rect₁ − rect₂ + 1 ≤ −1`. -/
theorem codimForm_concatMove_lt {m : Fin (N + 1) × Fin (N + 1) → ℕ} {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 1) (hcd : (c : ℕ) ≤ d') (ha1 : 1 ≤ (a : ℕ))
    (hsab : 1 ≤ m (a, b)) (hscd : 1 ≤ m (c, d')) :
    codimForm N (extendℤ (concatMove m a b c d')) < codimForm N (extendℤ m) := by
  set M := extendℤ m with hMdef
  have hbc' : (c : ℕ) = b + 1 := hbc
  rw [extendℤ_concatMove hab (by omega) hcd hsab hscd, codimForm_add,
    codimBil_concatDelta_right M hab hbc hcd ha1, codimBil_concatDelta_left M hab hbc hcd ha1,
    codimForm_concatDelta hab hbc hcd ha1]
  -- the two rectangles are ≥ their source entries
  have hnn : ∀ α β, 0 ≤ M α β := fun α β ↦ extendℤ_nonneg m α β
  have hi1 : ((a : ℤ) + 1) ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ) := by
    simp only [Finset.mem_Icc]; exact ⟨le_refl _, by exact_mod_cast (by omega : (a : ℕ) + 1 ≤ c)⟩
  have hic : (c : ℤ) ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ) := by
    simp only [Finset.mem_Icc]; exact ⟨by exact_mod_cast (by omega : (a : ℕ) + 1 ≤ c), le_refl _⟩
  have hjc : (c : ℤ) ∈ Finset.Icc (c : ℤ) (d' : ℤ) := by
    simp only [Finset.mem_Icc]; exact ⟨le_refl _, by exact_mod_cast hcd⟩
  have hjd : (d' : ℤ) ∈ Finset.Icc (c : ℤ) (d' : ℤ) := by
    simp only [Finset.mem_Icc]; exact ⟨by exact_mod_cast hcd, le_refl _⟩
  have hrect1 : (M (a : ℤ) (b : ℤ))
      ≤ ∑ i ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ),
          M (i - 1) (j - 1) := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i ↦ ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ), M (i - 1) (j - 1))
      (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hnn _ _)) hi1)
    refine le_trans ?_ (Finset.single_le_sum (f := fun j ↦ M (((a : ℤ) + 1) - 1) (j - 1))
      (fun j _ ↦ hnn _ _) hjc)
    -- the `(a+1, c)` entry is `M a b` (since `(a+1)-1 = a`, `c-1 = b`)
    simp only [add_sub_cancel_right]
    rw [show ((c : ℤ) - 1) = (b : ℤ) by push_cast [hbc']; ring]
  have hrect2 : (M (c : ℤ) (d' : ℤ))
      ≤ ∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ), M u v := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun u ↦ ∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ), M u v)
      (fun u _ ↦ Finset.sum_nonneg (fun v _ ↦ hnn _ _)) hic)
    exact Finset.single_le_sum (f := fun v ↦ M (c : ℤ) v) (fun v _ ↦ hnn _ _) hjd
  have h1ab : (1 : ℤ) ≤ M (a : ℤ) (b : ℤ) := by
    rw [hMdef, extendℤ_fin_eq m (by exact_mod_cast hab)]; exact_mod_cast hsab
  have h1cd : (1 : ℤ) ≤ M (c : ℤ) (d' : ℤ) := by
    rw [hMdef, extendℤ_fin_eq m (by exact_mod_cast hcd)]; exact_mod_cast hscd
  -- codimForm M + (−rect₁) + (−rect₂) + 1 < codimForm M
  have : codimForm N M + (- ∑ i ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ),
        ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ), M (i - 1) (j - 1))
      + (- ∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ), ∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ), M u v) + 1
      ≤ codimForm N M - 1 := by linarith
  linarith [this]

/-! ## The converse, top-level

`cCodim_ge_qipMin` is the reverse inequality; `cCodim_eq_qipMin` combines it with the easy `≤`.
`mOfE_surj_of_hl` and the exhaustiveness/minimiser-is-HL chain carry the work. -/

/-! ### HL ⟹ `mOfE`-image (the constructive inverse `eOfm`)

For a horizontal-lace `m`, read `e_i = m (0, i-1)` off the low-column multiplicities (`eOfm`). The
Kostant constraints then force `mOfE d (eOfm m) = m`: feasibility `∑ eOfm = d 0` is `kostantAt … 0`
(corner `0` drops the last term); the top-row entries are forced by the adjacent-vertex identity
`m (x, N) = m (0, x-1) + (d x − d (x-1))`; interior entries vanish by HL. -/

/-- The constructive inverse of `mOfE` on HL partitions: `eOfm m i = m (0, i.castSucc)` (paper
`e_i = m(0, i-1)`). -/
def eOfm (m : Fin (N + 1) × Fin (N + 1) → ℕ) : Fin N → ℕ :=
  fun i ↦ m (0, i.castSucc)

/-- **HL ⟹ in the `mOfE`-image.** For weakly-increasing `d`, every horizontal-lace Kostant partition
of `d` (corner `0`) is `mOfE d e` for some feasible `e` (`∑ e = d 0`); witness `e = eOfm m`. -/
theorem mOfE_surj_of_hl (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d 0) (hHL : IsHL m) :
    ∃ e : Fin N → ℕ, (∑ i, e i = d 0) ∧ mOfE d e = m := by
  rw [mem_kostantPartitions] at hm
  obtain ⟨hbnd, hsupp, hk, hcorner⟩ := hm
  refine ⟨eOfm m, ?_, ?_⟩
  · -- feasibility: `kostantAt … 0` says `d 0 = ∑_{p.1=0} m p = ∑_b m(0,b)`; corner drops the last.
    have h0 := hk 0
    rw [kostantAt] at h0
    -- the filter `p.1 ≤ 0 ∧ 0 ≤ p.2` is exactly `p.1 = 0`
    have hfilter : (Finset.univ.filter
          (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ 0 ∧ (0 : Fin (N + 1)) ≤ p.2))
        = Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = 0) := by
      apply Finset.filter_congr; intro p _
      simp only [Fin.le_zero_iff, Fin.zero_le, and_true]
    rw [hfilter] at h0
    -- `∑_{p.1=0} m p = ∑_{b : Fin(N+1)} m (0, b)`
    have hsum : (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = 0), m p)
        = ∑ b : Fin (N + 1), m (0, b) := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (0 : Fin (N + 1))]
      · simp
      · intro x _ hx; rw [Finset.sum_eq_zero]; intro b _; rw [if_neg (by simp [hx])]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, Fin.sum_univ_castSucc, hcorner, add_zero] at h0
    simp only [eOfm]; exact h0.symm
  · -- `mOfE d (eOfm m) = m`: low col = `eOfm`, corner `0`, interior `0` by HL, top row by `hid2`.
    -- adjacent-vertex identity (HL): for `1 ≤ x`, `m(x,last) + d(x-1) = m(0,x-1) + d x`.
    have hid2 : ∀ x : Fin (N + 1), 1 ≤ (x : ℕ) →
        m (x, Fin.last N) + d ⟨(x : ℕ) - 1, by omega⟩ = m (0, ⟨(x : ℕ) - 1, by omega⟩) + d x := by
      intro x hx
      set xm : Fin (N + 1) := ⟨(x : ℕ) - 1, by omega⟩ with hxm
      have hxmx : (x : ℕ) = (xm : ℕ) + 1 := by simp [hxm]; omega
      -- edge equality at `(xm, x)`: `d xm + Starts_xm = d x + Ends_xm` (cf. `ends_le_starts`)
      have hStarts : (∑ y : Fin (N + 1), m (x, y)) = m (x, Fin.last N) := by
        rw [Fin.sum_univ_castSucc]
        rw [Finset.sum_eq_zero (fun y _ ↦ hHL (x, y.castSucc) (by simpa using hx)
          (by rw [Fin.val_castSucc]; have := y.isLt; omega)), zero_add]
      have hEnds : (∑ z : Fin (N + 1), m (z, xm)) = m (0, xm) := by
        rw [Fin.sum_univ_succ]
        rw [Finset.sum_eq_zero (fun z _ ↦ hHL (z.succ, xm) (by rw [Fin.val_succ]; omega)
          (by simp [hxm]; omega)), add_zero]
      -- the per-vertex edge identity (same as in `ends_le_starts`)
      have hidxm := hk xm; have hidx := hk x
      rw [kostantAt] at hidxm hidx
      have hkey : (∑ p ∈ Finset.univ.filter
            (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ xm ∧ xm ≤ p.2), m p)
          + (∑ y : Fin (N + 1), m (x, y))
          = (∑ p ∈ Finset.univ.filter
            (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ x ∧ x ≤ p.2), m p)
            + ∑ z : Fin (N + 1), m (z, xm) := by
        rw [show (∑ y : Fin (N + 1), m (x, y))
            = ∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = x), m p from by
          rw [Finset.sum_filter, Fintype.sum_prod_type]
          rw [Finset.sum_eq_single x (fun z _ hzx ↦ Finset.sum_eq_zero
            (fun y _ ↦ by rw [if_neg (by simp [hzx])])) (fun h ↦ absurd (Finset.mem_univ _) h)]
          exact (Finset.sum_congr rfl (fun y _ ↦ by simp)).symm]
        rw [show (∑ z : Fin (N + 1), m (z, xm))
            = ∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.2 = xm), m p from by
          rw [Finset.sum_filter, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun z _ ↦ ?_)
          rw [Finset.sum_eq_single xm (fun y _ hyxm ↦ by rw [if_neg (by simp [hyxm])])
            (fun h ↦ absurd (Finset.mem_univ _) h)]
          simp]
        simp only [Finset.sum_filter]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun p _ ↦ ?_)
        by_cases hps : p.1 ≤ p.2
        · rw [Fin.le_def] at hps
          simp only [Fin.le_def, Fin.ext_iff]; split_ifs <;> omega
        · rw [hsupp p hps]; simp
      rw [hStarts, hEnds, ← hidxm, ← hidx] at hkey
      have hmono : d xm ≤ d x := hd (by rw [Fin.le_def]; omega)
      omega
    -- assemble `mOfE d (eOfm m) p = m p` by cases on `p`
    funext p; obtain ⟨x, y⟩ := p
    rcases Fin.eq_castSucc_or_eq_last y with ⟨yy, rfl⟩ | rfl
    · -- `y = yy.castSucc` (so `y < N`)
      have hyN : (yy.castSucc : Fin (N + 1)).val < N := by rw [Fin.val_castSucc]; exact yy.isLt
      by_cases hx0 : x = 0
      · subst hx0; rw [mOfE_zero_lt hyN]; simp only [eOfm]
        congr 2
      · -- `x ≥ 1`, `y < N`: interior, both sides `0`
        have hx1 : 1 ≤ (x : ℕ) := by have : (x : ℕ) ≠ 0 := fun h ↦ hx0 (Fin.ext h); omega
        have hyy : (yy.castSucc : Fin (N + 1)).val ≤ N - 1 := by
          rw [Fin.val_castSucc]; have := yy.isLt; omega
        rw [hHL (x, yy.castSucc) hx1 hyy]
        have hx0' : ((x, yy.castSucc) : Fin (N+1) × Fin (N+1)).1 ≠ 0 := by
          simp only [Fin.ne_iff_vne, Fin.val_zero]; omega
        have hyl' : ((x, yy.castSucc) : Fin (N+1) × Fin (N+1)).2 ≠ Fin.last N := by
          simp only [Fin.ne_iff_vne, Fin.val_last, Fin.val_castSucc]; have := yy.isLt; omega
        unfold mOfE
        rw [dif_neg (fun h ↦ hx0' h.1), dif_neg (fun h ↦ hyl' h.2), add_zero]
    · -- `y = last`
      by_cases hx0 : x = 0
      · subst hx0; rw [mOfE_corner, hcorner]
      · have hx1 : 1 ≤ (x : ℕ) := by have : (x : ℕ) ≠ 0 := fun h ↦ hx0 (Fin.ext h); omega
        rw [mOfE_top hx1]
        -- `eOfm m ⟨x-1⟩ + (d x − d ⟨x-1⟩) = m (x, last)` via `hid2`; `Fin.castSucc_mk` unifies idx.
        simp only [eOfm, Fin.castSucc_mk]
        have hid := hid2 x hx1
        have hmono : d ⟨(x : ℕ) - 1, by omega⟩ ≤ d x := hd (by rw [Fin.le_def]; simp)
        omega

/-! ### The concat move stays a valid corner-`0` Kostant partition

`[a,b] ⊎ [c,d'] = [a,d']` at vertex level (`c = b+1`): at each vertex `k`, exactly one of `[a,b]`,
`[c,d']` covers `k` whenever `[a,d']` does, so `+[a,d'] −[a,b] −[c,d']` leaves every vertex
sum unchanged. With `a ≥ 1` the corner stays `0`. -/

/-- **The concat move preserves membership.** For `a ≤ b`, `c = b+1`, `c ≤ d'`, `a ≥ 1`, sources
present, `concatMove m a b c d' ∈ kostantPartitions d 0` whenever `m` is. -/
theorem concatMove_mem {d : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {a b c d' : Fin (N + 1)} (hm : m ∈ kostantPartitions d 0)
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 1) (hcd : (c : ℕ) ≤ d') (ha1 : 1 ≤ (a : ℕ))
    (hsab : 1 ≤ m (a, b)) (hscd : 1 ≤ m (c, d')) :
    concatMove m a b c d' ∈ kostantPartitions d 0 := by
  rw [mem_kostantPartitions] at hm ⊢
  obtain ⟨hbnd, hsupp, hk, hcorner⟩ := hm
  -- the three changed keys are pairwise distinct
  have hkeyAD_AB : ((a, d') : Fin (N+1) × Fin (N+1)) ≠ (a, b) := by
    simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun _ h ↦ by
      have : (d' : ℕ) ≠ b := by omega
      exact this (by rw [h])
  have hkeyAD_CD : ((a, d') : Fin (N+1) × Fin (N+1)) ≠ (c, d') := by
    simp only [ne_eq, Prod.mk.injEq, not_and]; intro h
    exact absurd (by rw [h] : (a:ℕ) = c) (by omega)
  have hkeyAB_CD : ((a, b) : Fin (N+1) × Fin (N+1)) ≠ (c, d') := by
    simp only [ne_eq, Prod.mk.injEq, not_and]; intro h
    exact absurd (by rw [h] : (a:ℕ) = c) (by omega)
  -- corner: none of the 3 keys is `(0, last)` (each has first index ≥ 1, or...)
  have hcornerKeys : ∀ p : Fin (N+1) × Fin (N+1), p = (0, Fin.last N) →
      concatMove m a b c d' p = m p := by
    intro p hp
    have h0a : (0 : Fin (N + 1)) ≠ a := by rw [Fin.ne_iff_vne, Fin.val_zero]; omega
    have h0c : (0 : Fin (N + 1)) ≠ c := by rw [Fin.ne_iff_vne, Fin.val_zero]; omega
    have h1 : p ≠ (a, d') := by
      rw [hp]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun h ↦ absurd h h0a
    have h2 : p ≠ (a, b) := by
      rw [hp]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun h ↦ absurd h h0a
    have h3 : p ≠ (c, d') := by
      rw [hp]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun h ↦ absurd h h0c
    simp only [concatMove, if_neg h1, if_neg h2, if_neg h3, add_zero, Nat.sub_zero]
  -- support: off the triangle, all 3 keys are on-triangle, so `concatMove p = m p = 0`
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → concatMove m a b c d' p = 0 := by
    intro p hp
    have h1 : p ≠ (a, d') := by
      rintro rfl; exact hp (by rw [Fin.le_def]; exact_mod_cast (by omega : (a:ℕ) ≤ d'))
    have h2 : p ≠ (a, b) := by rintro rfl; exact hp (by rw [Fin.le_def]; exact_mod_cast hab)
    have h3 : p ≠ (c, d') := by rintro rfl; exact hp (by rw [Fin.le_def]; exact_mod_cast hcd)
    simp only [concatMove, if_neg h1, if_neg h2, if_neg h3, add_zero, Nat.sub_zero]
    exact hsupp p hp
  -- per-key ℤ-cast of the move: honest subtraction (sources ≥ 1, keys distinct)
  have hcastpt : ∀ p, ((concatMove m a b c d' p : ℕ) : ℤ)
      = (m p : ℤ) + (if p = (a, d') then 1 else 0)
        - (if p = (a, b) then 1 else 0) - (if p = (c, d') then 1 else 0) := by
    intro p
    by_cases h1 : p = (a, d')
    · subst h1
      rw [if_pos rfl, if_neg hkeyAD_AB, if_neg hkeyAD_CD]
      simp only [concatMove, if_neg hkeyAD_AB, if_neg hkeyAD_CD, Nat.sub_zero]
      push_cast; ring
    · by_cases h2 : p = (a, b)
      · subst h2
        rw [if_neg h1, if_pos rfl, if_neg hkeyAB_CD]
        simp only [concatMove, if_neg h1, if_neg hkeyAB_CD, add_zero, Nat.sub_zero, if_true]
        rw [Nat.cast_sub hsab]; push_cast; ring
      · by_cases h3 : p = (c, d')
        · subst h3
          rw [if_neg h1, if_neg h2, if_pos rfl]
          simp only [concatMove, if_neg h1, if_neg h2, add_zero, Nat.sub_zero, if_true]
          rw [Nat.cast_sub hscd]; push_cast; ring
        · rw [if_neg h1, if_neg h2, if_neg h3]
          simp only [concatMove, if_neg h1, if_neg h2, if_neg h3, add_zero, Nat.sub_zero]
          ring
  -- Kostant preservation at every vertex: the filtered sum is unchanged.
  have hk' : ∀ k, kostantAt d (concatMove m a b c d') k := by
    intro k
    have hkk := hk k
    rw [kostantAt] at hkk ⊢
    rw [hkk]
    set F := Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2) with hF
    -- cast both vertex sums to ℤ; the indicator sums are membership flags, net `0`.
    refine Nat.cast_injective (R := ℤ) ?_
    push_cast
    rw [Finset.sum_congr rfl (fun p _ ↦ hcastpt p)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    -- each indicator sum is `1` if the key ∈ F else `0`
    rw [Finset.sum_ite_eq' F (a, d'), Finset.sum_ite_eq' F (a, b), Finset.sum_ite_eq' F (c, d')]
    -- membership in F = vertex coverage; the net of the three flags is `0`
    have hmemAD : ((a, d') ∈ F) ↔ (a ≤ k ∧ k ≤ d') := by simp [hF]
    have hmemAB : ((a, b) ∈ F) ↔ (a ≤ k ∧ k ≤ b) := by simp [hF]
    have hmemCD : ((c, d') ∈ F) ↔ (c ≤ k ∧ k ≤ d') := by simp [hF]
    by_cases hkAD : a ≤ k ∧ k ≤ d'
    · by_cases hkAB : a ≤ k ∧ k ≤ b
      · rw [if_pos (hmemAD.mpr hkAD), if_pos (hmemAB.mpr hkAB),
          if_neg (fun h ↦ by have := hmemCD.mp h; rw [Fin.le_def, Fin.le_def] at *; omega)]
        ring
      · rw [if_pos (hmemAD.mpr hkAD), if_neg (fun h ↦ hkAB (hmemAB.mp h)),
          if_pos (hmemCD.mpr (by
            rw [Fin.le_def, Fin.le_def] at *; push_neg at hkAB; constructor <;> omega))]
        ring
    · rw [if_neg (fun h ↦ hkAD (hmemAD.mp h)),
        if_neg (fun h ↦ by have := hmemAB.mp h; rw [Fin.le_def, Fin.le_def] at *; omega),
        if_neg (fun h ↦ by have := hmemCD.mp h; rw [Fin.le_def, Fin.le_def] at *; omega)]
      ring
  exact ⟨bound_of_kostant hsupp' hk', hsupp', hk', by
    rw [hcornerKeys _ rfl]; exact hcorner⟩

/-- **The edge inequality (right partner exists).** For monotone `d`, KP `m`, an interval ending at
`b`, `c = b+1`: `Ends_b ≤ Starts_b`, i.e. `∑_x m(x,b) ≤ ∑_y m(c,y)`. From `d b ≤ d c` + per-vertex
identity `1_{Fb} + 1_{p.1=c} = 1_{Fc} + 1_{p.2=b}` (on the support triangle). -/
theorem ends_le_starts {d : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm : m ∈ kostantPartitions d 0) (hd : Monotone d) {b c : Fin (N + 1)} (hbc : (c : ℕ) = b + 1) :
    (∑ x : Fin (N + 1), m (x, b)) ≤ ∑ y : Fin (N + 1), m (c, y) := by
  rw [mem_kostantPartitions] at hm
  obtain ⟨-, hsupp, hk, -⟩ := hm
  have hdbc : d b ≤ d c := hd (by rw [Fin.le_def]; omega)
  -- `d b = ∑_{Fb} m`, `d c = ∑_{Fc} m`; the per-vertex identity gives `d b + Starts = d c + Ends`.
  have hidb := hk b; have hidc := hk c
  rw [kostantAt] at hidb hidc
  -- prove `d b + Starts = d c + Ends` by a single `Finset.sum` over `univ`.
  have hStarts : (∑ y : Fin (N + 1), m (c, y))
      = ∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = c), m p := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    conv_rhs => rw [Finset.sum_eq_single c (fun x _ hxc ↦ Finset.sum_eq_zero
      (fun y _ ↦ by rw [if_neg (by simp [hxc])])) (fun h ↦ absurd (Finset.mem_univ _) h)]
    exact (Finset.sum_congr rfl (fun y _ ↦ by simp)).symm
  have hEnds : (∑ x : Fin (N + 1), m (x, b))
      = ∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.2 = b), m p := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hyb; rw [if_neg (by simp [hyb])]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- the per-vertex identity: `∑_{Fb} m + ∑_{p.1=c} m = ∑_{Fc} m + ∑_{p.2=b} m`
  have hkey :
      (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ b ∧ b ≤ p.2), m p)
      + (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = c), m p)
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ c ∧ c ≤ p.2), m p)
        + ∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.2 = b), m p := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ ↦ ?_)
    -- on support (`p.1 ≤ p.2`), coefficient identity by `omega`; off support `m p = 0`.
    by_cases hps : p.1 ≤ p.2
    · rw [Fin.le_def] at hps
      have hbc' : (c : ℕ) = b + 1 := hbc
      simp only [Fin.le_def, Fin.ext_iff]
      split_ifs <;> omega
    · rw [hsupp p hps]; simp
  rw [hStarts, hEnds, ← hidb, ← hidc] at *
  omega

/-- **Minimiser ⟹ horizontal-lace.** For weakly-increasing `d`, any partition attaining the
minimum `cCodim d 0` is horizontal-lace (else a strictly-decreasing valid move contradicts it). -/
theorem minimiser_isHL (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm : m ∈ kostantPartitions d 0) (hmin : codimForm N (extendℤ m) = cCodim d 0 h) :
    IsHL m := by
  by_contra hnHL
  -- a non-HL `m` has an interior interval `[a,b]` with `m(a,b) ≥ 1`
  rw [IsHL] at hnHL; push_neg at hnHL
  obtain ⟨p, ha1, hbN, hpos⟩ := hnHL
  obtain ⟨a, b⟩ := p
  simp only at ha1 hbN hpos
  -- the partner: `c = b+1`, `Starts_b ≥ Ends_b ≥ m(a,b) ≥ 1`, so some `m(c, d') ≥ 1`
  have haN : (a : ℕ) ≤ N := by have := a.isLt; omega
  have hbN' : (b : ℕ) < N := by omega
  set c : Fin (N + 1) := ⟨(b : ℕ) + 1, by omega⟩ with hc
  have hbc : (c : ℕ) = b + 1 := by simp [hc]
  have hpos1 : 1 ≤ m (a, b) := Nat.one_le_iff_ne_zero.mpr hpos
  have hableq : (a : ℕ) ≤ b := by
    by_contra hlt
    exact hpos ((mem_kostantPartitions.mp hm).2.1 (a, b) (by simp only [Fin.le_def]; omega))
  have hEnds1 : 1 ≤ ∑ x : Fin (N + 1), m (x, b) :=
    le_trans hpos1 (Finset.single_le_sum (f := fun x ↦ m (x, b)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ a))
  have hStarts1 : 1 ≤ ∑ y : Fin (N + 1), m (c, y) :=
    le_trans hEnds1 (ends_le_starts hm hd hbc)
  obtain ⟨d', -, hd'pos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : (∑ y, m (c, y)) ≠ 0)
  -- `m (c, d') ≥ 1`; support forces `c ≤ d'`
  have hcd : (c : ℕ) ≤ d' := by
    by_contra hlt
    rw [(mem_kostantPartitions.mp hm).2.1 (c, d') (by simp only [Fin.le_def]; omega)] at hd'pos
    exact hd'pos rfl
  have hscd : 1 ≤ m (c, d') := Nat.one_le_iff_ne_zero.mpr hd'pos
  -- the concat move strictly drops `codimForm`, but `m` minimises — contradiction with `inf'_le`.
  have hmem := concatMove_mem hm hableq hbc hcd ha1 hpos1 hscd
  have hlt := codimForm_concatMove_lt (m := m) hableq hbc hcd ha1 hpos1 hscd
  rw [hmin] at hlt
  exact absurd (Finset.inf'_le (s := kostantPartitions d 0) (fun m ↦ codimForm N (extendℤ m)) hmem)
    (not_le.mpr hlt)

/-- **The QIP converse `≥` (Thm 6.1).** For weakly-increasing `d`, `qipMin d ≤ cCodim d 0`: a
minimiser is HL (`minimiser_isHL`), hence in the `mOfE`-image
(`mOfE_surj_of_hl`), hence its `codimForm` value is some `Gqip d e ≥ qipMin d`. -/
theorem cCodim_ge_qipMin (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    qipMin d hne ≤ cCodim d 0 h := by
  -- the minimum is attained at some `m ∈ kostantPartitions d 0`
  obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_inf' h (fun m ↦ codimForm N (extendℤ m))
  rw [cCodim, hmeq]
  -- `m` minimises, so it is HL, so `m = mOfE d e` for a feasible `e`
  have hHL : IsHL m := minimiser_isHL d hd h hm hmeq.symm
  obtain ⟨e, he, hme⟩ := mOfE_surj_of_hl d hd hm hHL
  -- `codimForm m = codimForm (mOfE d e) = Gqip d e`, and `Gqip d e ≥ qipMin`
  rw [← hme, codimForm_mOfE d hd e, qipMin]
  refine Finset.inf'_le (Gqip d) ?_
  rw [qipFeasible, Finset.mem_finAntidiagonal]; exact he

/-- **The QIP (Thm 6.1), as equality.** For weakly-increasing `d`, `cCodim d 0 = qipMin d`: the
combinatorial codimension of the zero-product locus equals the QIP minimum. (The per-orbit geometric
reading of `cCodim` is proved in `Core.CThetaGeometric`; the `Σ̄^r`-aggregate reading
`codim Σ̄^r = cCodim d r` is proved in `Core.SigmaCodim` — as in `Core.CTheta`.) -/
theorem cCodim_eq_qipMin (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    cCodim d 0 h = qipMin d hne :=
  le_antisymm (cCodim_le_qipMin d hd h hne) (cCodim_ge_qipMin d hd h hne)

/-- **Witness `(2,2,2)`: `cCodim = qipMin = 3` (Thm 6.1, full equality).** The closed QIP on the
zero-product locus of `(2,2,2)`, matching `Core.CTheta.cCodim_d222_zero` and
`Core.CThetaQIP.qipMin_d222_eq_three`. -/
theorem cCodim_eq_qipMin_d222 :
    cCodim d222 0 kostantPartitions_d222_nonempty = qipMin d222 qipFeasible_d222_nonempty :=
  cCodim_eq_qipMin d222 d222_monotone _ _

end DLNFibre.Core
