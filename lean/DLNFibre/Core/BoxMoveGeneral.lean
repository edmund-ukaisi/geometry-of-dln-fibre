import DLNFibre.Core.BoxMoveDegeneration

/-!
# `DLNFibre.Core.BoxMoveGeneral` — the general box-move degeneration (L6.1-general)

Two building blocks above the landed degeneration engine
`mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily`, generalising the certified `(1,2,1)`
witness of `DLNFibre.Core.BoxMoveDegeneration` towards the full box move (`a < c ≤ b+1 ≤ e`,
arbitrary `rest`):

* **Common-summand lemma** (`mem_closure_dirSum_of_mem_closure`): if the downstairs flattening of
  `D₀` lies in the Zariski closure of the orbit of `U₀` (via *any* polynomial family), then the same
  holds for `dirSum D₀ R`/`dirSum U₀ R` with a common block-diagonal summand `R`. The degeneration
  family is `dirSumPoly F₀ (const R)` (block-diagonal, `R` fixed) and the `t ≠ 0` base change is
  `P₀ ⊕ 1_R` (`liftDirSumBaseChange`: `P₀` on the first block, identity on the common `R`). This
  isolates `rest` from the symbolic two-interval move.

* **Split box move** (`splitCut_mem_closure`, `splitCut_orbit_intervalDirectSum`): the split case
  `c = b+1` with no `rest` — `M_{[a,e]} ⇝ M_{[a,b]} ⊕ M_{[b+1,e]}` for arbitrary intervals, via the
  cut chain `splitCut a e b` and the explicit diagonal base change `splitBaseChange`. The
  **non-split** case (`c ≤ b`, dim-2 overlap) and the list-gluing to `intervalDirectSum
  (Lmove ++ rest)` are the remaining gap above these two blocks (see the thread report).

The mechanism reuses the block-diagonal levers of `Core.IntervalModule` (`reindex_fromBlocks_mul`,
`reindex_fromBlocks_one`).

**Typeclass.** `[Field k]` for the orbit certificate, `[Infinite k]` for the engine. **Dependency
rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Direct sum of polynomial-coefficient tuples and the constant polynomial tuple -/

/-- The direct sum of two polynomial-coefficient tuples, block-diagonal per edge. -/
noncomputable def dirSumPoly {d d' : Fin (N + 1) → ℕ}
    (A : Tuple (k := Polynomial k) d) (B : Tuple (k := Polynomial k) d') :
    Tuple (k := Polynomial k) (fun l ↦ d l + d' l) :=
  dirSum A B

/-- The constant polynomial tuple of a `k`-tuple `R`: each entry `C (R i r c)`. -/
noncomputable def constPoly {d : Fin (N + 1) → ℕ} (R : Tuple (k := k) d) :
    Tuple (k := Polynomial k) d :=
  fun i ↦ (R i).map Polynomial.C

/-- `tupleEval (constPoly R) t = R`: the constant tuple evaluates to `R` at every `t`. -/
theorem tupleEval_constPoly {d : Fin (N + 1) → ℕ} (R : Tuple (k := k) d) (t : k) :
    tupleEval (constPoly R) t = R := by
  funext i r c
  simp only [tupleEval, constPoly, Matrix.map_apply, Polynomial.eval_C]

/-- `tupleEval` commutes with `dirSum`: `tupleEval (dirSumPoly A B) t = dirSum (tupleEval A t)
(tupleEval B t)`. -/
theorem tupleEval_dirSumPoly {d d' : Fin (N + 1) → ℕ}
    (A : Tuple (k := Polynomial k) d) (B : Tuple (k := Polynomial k) d') (t : k) :
    tupleEval (dirSumPoly A B) t = dirSum (tupleEval A t) (tupleEval B t) := by
  funext i r c
  simp only [tupleEval, dirSumPoly, dirSum, Matrix.map_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm r with r' | r' <;> rcases finSumFinEquiv.symm c with c' | c' <;>
    simp [Matrix.fromBlocks]

/-! ## The block-diagonal base change `P ⊕ 1` and its action -/

/-- The block-diagonal unit `P ⊕ 1` at each vertex: `reindex (fromBlocks (P v) 0 0 1)`, with inverse
`reindex (fromBlocks (P v)⁻¹ 0 0 1)`. The base change that acts as `P` on the first block and the
identity on the (common) second block. -/
noncomputable def liftDirSumBaseChange {d d' : Fin (N + 1) → ℕ}
    (P : BaseChangeGroup (k := k) d) : BaseChangeGroup (k := k) (fun l ↦ d l + d' l) :=
  fun v ↦
  { val := Matrix.reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks (Units.val (P v)) 0 0 (1 : Matrix (Fin (d' v)) (Fin (d' v)) k))
    inv := Matrix.reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks (Units.val (P v)⁻¹) 0 0 (1 : Matrix (Fin (d' v)) (Fin (d' v)) k))
    val_inv := by
      rw [reindex_fromBlocks_mul, Units.mul_inv, Matrix.one_mul, ← reindex_fromBlocks_one]
    inv_val := by
      rw [reindex_fromBlocks_mul, Units.inv_mul, Matrix.one_mul, ← reindex_fromBlocks_one] }

/-- **The lifted base change acts block-wise.** `(P ⊕ 1) • (dirSum A B) = dirSum (P • A) B`. -/
theorem liftDirSumBaseChange_smul {d d' : Fin (N + 1) → ℕ}
    (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) (B : Tuple (k := k) d') :
    liftDirSumBaseChange (d' := d') P • dirSum A B = dirSum (P • A) B := by
  funext i
  rw [smul_eq_baseChange, baseChange_apply, smul_eq_baseChange, dirSum, dirSum, baseChange_apply]
  rw [show Units.val (liftDirSumBaseChange (d' := d') P i.succ)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks (Units.val (P i.succ)) 0 0 (1 : Matrix (Fin (d' i.succ)) (Fin (d' i.succ)) k))
    from rfl]
  rw [show Units.val (liftDirSumBaseChange (d' := d') P i.castSucc)⁻¹
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks (Units.val (P i.castSucc)⁻¹) 0 0
          (1 : Matrix (Fin (d' i.castSucc)) (Fin (d' i.castSucc)) k))
    from rfl]
  rw [reindex_fromBlocks_mul, reindex_fromBlocks_mul, Matrix.mul_one, Matrix.one_mul]

/-! ## The common-summand lemma -/

/-- **The common-summand lemma (L6.1, the `rest` reduction).** If `D₀`'s flattening lies in the
Zariski closure of the orbit of `U₀` — witnessed by a polynomial family `F₀` with limit `D₀` and
`t ≠ 0` orbit membership — then for any common summand `R` the flattening of `dirSum D₀ R` lies in
the Zariski closure of the orbit of `dirSum U₀ R`. The degeneration family is `dirSumPoly F₀
(const R)` (block-diagonal, `R` fixed); the `t ≠ 0` base change is `P₀(t) ⊕ 1_R`. Lets the appended
`rest` of a box move ride as a fixed direct summand, isolating the symbolic two-interval move. -/
theorem mem_closure_dirSum_of_mem_closure [Infinite k] {d d' : Fin (N + 1) → ℕ}
    (U₀ D₀ : Tuple (k := k) d) (R : Tuple (k := k) d') (F₀ : Tuple (k := Polynomial k) d)
    (h0 : tupleEval F₀ 0 = D₀)
    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U₀ = tupleEval F₀ t) :
    canonicalCoord (fun l ↦ d l + d' l) (dirSum D₀ R)
      ∈ MvPolynomial.zeroLocus (σ := RepCoord (fun l ↦ d l + d' l)) (k := k) k
          (MvPolynomial.vanishingIdeal (σ := RepCoord (fun l ↦ d l + d' l)) (K := k) k
            (orbitSet (dirSum U₀ R))) := by
  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily (dirSum U₀ R) (dirSum D₀ R)
    (dirSumPoly F₀ (constPoly R)) ?_ (fun t ht ↦ ?_)
  · rw [tupleEval_dirSumPoly, tupleEval_constPoly, h0]
  · obtain ⟨P, hP⟩ := horb t ht
    refine ⟨liftDirSumBaseChange (d' := d') P, ?_⟩
    rw [liftDirSumBaseChange_smul, hP, tupleEval_dirSumPoly, tupleEval_constPoly]

/-! ## The split box move `M_{[a,e]} ⇝ M_{[a,b]} ⊕ M_{[b+1,e]}` (`c = b+1`, no rest)

The split case `c = b+1` of the box move with no common summand: the single interval module
`M_{[a,e]}` (the all-identity chain on `[a,e]`) degenerates to the **cut chain** `splitCut a e b` —
the same chain with the edge `b → b+1` set to zero. As tuples both live over the *single* dimension
vector `intervalDim a e` (no transport), differing only at edge `b`. The cut chain has the rank
pattern of `M_{[a,b]} ⊕ M_{[b+1,e]}` (`rankPattern_splitCut`), so it realizes the split downstairs;
the headline lands its flattening in the Zariski closure of the orbit of `M_{[a,e]}`. -/

/-- The **cut chain** `splitCut a e b`: the interval module `M_{[a,e]}` with the single edge `b`
zeroed. The split downstairs `M_{[a,b]} ⊕ M_{[b+1,e]}` realized over the dimension vector
`intervalDim a e` (the partition `[a,b] ⊔ [b+1,e] = [a,e]` preserves it). -/
def splitCut (a e : Fin (N + 1)) (b : Fin N) : Tuple (k := k) (intervalDim a e) :=
  fun t ↦ if t = b then 0 else intervalModule a e t

/-- The **split degeneration family**: `M_{[a,e]}` with edge `b` carrying the parameter `X`. Its
`eval`-at-`t` is the chain with edge `b` scaled by `t`; at `t = 0` it is the cut chain. -/
noncomputable def splitFamilyPoly (a e : Fin (N + 1)) (b : Fin N) :
    Tuple (k := Polynomial k) (intervalDim a e) :=
  fun s r c ↦ if s = b then (if intervalActive a e s then Polynomial.X else 0)
    else Polynomial.C (intervalModule a e s r c)

/-- At `t = 0` the split family is the cut chain (`X ↦ 0` zeroes edge `b`). -/
theorem tupleEval_splitFamilyPoly_zero (a e : Fin (N + 1)) (b : Fin N) :
    tupleEval (splitFamilyPoly (k := k) a e b) 0 = splitCut a e b := by
  funext s r c
  simp only [tupleEval, splitFamilyPoly, splitCut, Matrix.map_apply]
  by_cases hs : s = b
  · subst hs
    simp only [intervalModule]
    by_cases hb : intervalActive a e s <;> simp [hb]
  · simp only [if_neg hs, Polynomial.eval_C]

/-- The `eval`-at-`t` of the split family at edge `s ≠ b` is the interval module's edge
(unchanged). -/
theorem tupleEval_splitFamilyPoly_ne (a e : Fin (N + 1)) (b : Fin N) (t : k) {s : Fin N}
    (hs : s ≠ b) : tupleEval (splitFamilyPoly (k := k) a e b) t s = intervalModule a e s := by
  funext r c
  simp only [tupleEval, splitFamilyPoly, if_neg hs, Matrix.map_apply, Polynomial.eval_C]

/-- The `eval`-at-`t` of the split family at edge `b` is `t` times the interval module's edge. -/
theorem tupleEval_splitFamilyPoly_self (a e : Fin (N + 1)) (b : Fin N) (t : k) :
    tupleEval (splitFamilyPoly (k := k) a e b) t b = t • intervalModule a e b := by
  funext r c
  simp only [tupleEval, splitFamilyPoly, Matrix.map_apply, Matrix.smul_apply, intervalModule]
  by_cases hb : intervalActive a e b
  · simp [hb]
  · simp [hb]

/-! ## The `t ≠ 0` orbit certificate for the split move

A diagonal base change carries `M_{[a,e]}` to the `t`-scaled family: the vertex unit is the
identity at vertices `≤ b` and the scalar `t` (`t • 1`, a unit for `t ≠ 0`) at vertices `> b`. The
conjugation `Q_{l+1} · 1 · Q_l⁻¹` is `1` on every edge except `b`, where it picks up the single
`t / 1 = t` jump (`Q_{b+1} = t`, `Q_b = 1`). -/

/-- The scalar unit `t • 1` on `Fin n`, with inverse `t⁻¹ • 1` (`t ≠ 0`). -/
def scalarUnit (n : ℕ) {t : k} (ht : t ≠ 0) : (Matrix (Fin n) (Fin n) k)ˣ where
  val := t • (1 : Matrix (Fin n) (Fin n) k)
  inv := t⁻¹ • (1 : Matrix (Fin n) (Fin n) k)
  val_inv := by rw [smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ ht, one_smul]
  inv_val := by rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ ht, one_smul]

/-- The diagonal split base change: identity at vertices `≤ b`, scalar `t` at vertices `> b`. -/
noncomputable def splitBaseChange (a e : Fin (N + 1)) (b : Fin N) {t : k} (ht : t ≠ 0) :
    BaseChangeGroup (k := k) (intervalDim a e) :=
  fun l ↦ if b.castSucc < l then scalarUnit (intervalDim a e l) ht else 1

/-- The matrix value of the split base change at `l`. -/
theorem splitBaseChange_val (a e : Fin (N + 1)) (b : Fin N) {t : k} (ht : t ≠ 0)
    (l : Fin (N + 1)) :
    (Units.val (splitBaseChange a e b ht l) : Matrix (Fin (intervalDim a e l)) _ k)
      = if b.castSucc < l then t • 1 else 1 := by
  rw [splitBaseChange]
  by_cases h : b.castSucc < l <;> simp [h, scalarUnit]

/-- The inverse matrix value of the split base change at `l`. -/
theorem splitBaseChange_inv_val (a e : Fin (N + 1)) (b : Fin N) {t : k} (ht : t ≠ 0)
    (l : Fin (N + 1)) :
    (Units.val (splitBaseChange a e b ht l)⁻¹ : Matrix (Fin (intervalDim a e l)) _ k)
      = if b.castSucc < l then t⁻¹ • 1 else 1 := by
  rw [splitBaseChange]
  by_cases h : b.castSucc < l
  · rw [if_pos h, if_pos h, ← Units.inv_eq_val_inv]; rfl
  · rw [if_neg h, if_neg h, inv_one, Units.val_one]

/-- **The `t ≠ 0` orbit certificate.** The diagonal base change carries `M_{[a,e]}` to the
`t`-scaled split family `tupleEval (splitFamilyPoly a e b) t`. -/
theorem splitBaseChange_smul (a e : Fin (N + 1)) (b : Fin N) {t : k} (ht : t ≠ 0) :
    splitBaseChange a e b ht • intervalModule (k := k) a e
      = tupleEval (splitFamilyPoly a e b) t := by
  funext s
  rw [smul_eq_baseChange, baseChange_apply, splitBaseChange_val, splitBaseChange_inv_val]
  -- the threshold predicate `b.castSucc < ·` in `Fin.val` terms: `b < l.val`
  have hval : ∀ l : Fin (N + 1), (b.castSucc < l) ↔ (b : ℕ) < (l : ℕ) := fun l ↦ by
    rw [Fin.lt_def, Fin.val_castSucc]
  by_cases hsb : s = b
  · -- the cut edge: `s.succ > b`, `s.castSucc = b ≤ b`, conjugation picks up `t`
    rw [hsb, tupleEval_splitFamilyPoly_self]
    have h1 : b.castSucc < b.succ := by rw [hval, Fin.val_succ]; omega
    have h2 : ¬ b.castSucc < b.castSucc := lt_irrefl _
    rw [if_pos h1, if_neg h2, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  · -- non-cut edge: both endpoints on the same side of `b`, conjugation is the identity
    rw [tupleEval_splitFamilyPoly_ne a e b t hsb]
    have hsbval : (s : ℕ) ≠ (b : ℕ) := fun h ↦ hsb (Fin.val_injective h)
    by_cases hlt : b.castSucc < s.castSucc
    · have hlt' : (b : ℕ) < (s : ℕ) := by rw [hval s.castSucc, Fin.val_castSucc] at hlt; exact hlt
      have h1 : b.castSucc < s.succ := by rw [hval, Fin.val_succ]; omega
      rw [if_pos h1, if_pos hlt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
        Matrix.mul_one, smul_smul, inv_mul_cancel₀ ht, one_smul]
    · have hge : ¬ (b : ℕ) < (s : ℕ) := by rw [hval s.castSucc, Fin.val_castSucc] at hlt; exact hlt
      have h1 : ¬ b.castSucc < s.succ := by rw [hval, Fin.val_succ]; omega
      rw [if_neg h1, if_neg hlt, Matrix.mul_one, Matrix.one_mul]

/-- For `t ≠ 0`, the `t`-scaled split family lies in the orbit of `M_{[a,e]}` (the `t ≠ 0`
membership feeding the engine). -/
theorem tupleEval_splitFamilyPoly_mem_orbit (a e : Fin (N + 1)) (b : Fin N) {t : k} (ht : t ≠ 0) :
    ∃ P : BaseChangeGroup (k := k) (intervalDim a e),
      P • intervalModule (k := k) a e = tupleEval (splitFamilyPoly a e b) t :=
  ⟨splitBaseChange a e b ht, splitBaseChange_smul a e b ht⟩

/-- **The split box move (L6.1-general, split case, no rest).** Over an infinite field, the
flattening of the cut chain `splitCut a e b` (the split downstairs `M_{[a,b]} ⊕ M_{[b+1,e]}`
realized over `intervalDim a e`) lies in the Zariski closure of the orbit of the interval module
`M_{[a,e]}`: it is in `zeroLocus (vanishingIdeal (orbitSet (intervalModule a e)))`. An instance of
the degeneration engine: the split family `splitFamilyPoly` has limit the cut chain at `t = 0` and
every `t ≠ 0` point in `orbit (M_{[a,e]})` (`tupleEval_splitFamilyPoly_mem_orbit`). -/
theorem splitCut_mem_closure [Infinite k] (a e : Fin (N + 1)) (b : Fin N) :
    canonicalCoord (intervalDim a e) (splitCut a e b)
      ∈ MvPolynomial.zeroLocus (σ := RepCoord (intervalDim a e)) (k := k) k
          (MvPolynomial.vanishingIdeal (σ := RepCoord (intervalDim a e)) (K := k) k
            (orbitSet (intervalModule a e))) := by
  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily (intervalModule a e)
    (splitCut a e b) (splitFamilyPoly a e b) (tupleEval_splitFamilyPoly_zero a e b) (fun t ht ↦ ?_)
  exact tupleEval_splitFamilyPoly_mem_orbit a e b ht

/-! ## The cut chain realizes the split downstairs (rank-pattern fidelity)

The cut chain `splitCut a e b` has the rank pattern of the genuine split downstairs `M_{[a,b]} ⊕
M_{[b+1,e]}` (for `a ≤ b` and `b+1 ≤ e`): a sub-product `A_j ⋯ A_{i+1}` is the `1×1` identity when
`[i,j] ⊆ [a,e]` and the path does **not** cross the cut edge `b`, and `0` otherwise. By the complete
invariant this makes `splitCut` `G_d`-equivalent to the interval direct sum
`M_{[a,b]} ⊕ M_{[b+1,e]}`, so the headline genuinely degenerates `M_{[a,e]}` to the split sum. -/

/-- `splitCut a e b` agrees with `intervalModule a e` off the cut edge `b`. -/
theorem splitCut_apply_ne (a e : Fin (N + 1)) (b : Fin N) {s : Fin N} (hs : s ≠ b) :
    splitCut (k := k) a e b s = intervalModule a e s := by
  rw [splitCut, if_neg hs]

/-- `splitCut a e b` is zero on the cut edge `b`. -/
theorem splitCut_apply_self (a e : Fin (N + 1)) (b : Fin N) :
    splitCut (k := k) a e b b = 0 := by
  rw [splitCut, if_pos rfl]

/-- **Sub-product of the cut chain, off the cut.** If the path `[i,j]` does not cross the cut edge
`b` (`¬ (i ≤ b.castSucc ∧ b.succ ≤ j)`), the cut chain's sub-product agrees with `M_{[a,e]}`'s. -/
theorem submult_splitCut_eq_of_not_cross (a e : Fin (N + 1)) (b : Fin N) {i j : Fin (N + 1)}
    (hij : i ≤ j) (hcross : ¬ (i ≤ b.castSucc ∧ b.succ ≤ j)) :
    submult (intervalDim a e) (splitCut (k := k) a e b) i j hij
      = submult (intervalDim a e) (intervalModule a e) i j hij := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := Fin.le_zero_iff.mp hij
    rw [submult_self, submult_self]
  | succ p ih =>
    rcases eq_or_lt_of_le hij with heq | hlt
    · obtain rfl := heq; rw [submult_self, submult_self]
    · have hip : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      -- the top edge `p` is not the cut (else the path would cross), and the rest does not cross
      have hpne : p ≠ b := by
        rintro rfl
        exact hcross ⟨hip, le_refl _⟩
      have hsub : ¬ (i ≤ b.castSucc ∧ b.succ ≤ p.castSucc) := by
        rintro ⟨h1, h2⟩
        exact hcross ⟨h1, le_trans h2 (Fin.castSucc_le_succ p)⟩
      rw [submult_succ (intervalDim a e) (splitCut a e b) i p hip,
        submult_succ (intervalDim a e) (intervalModule a e) i p hip,
        ih hip hsub, splitCut_apply_ne a e b hpne]

/-- **Sub-product of the cut chain, across the cut.** If the path `[i,j]` crosses the cut edge `b`
(`i ≤ b.castSucc ∧ b.succ ≤ j`), the cut chain's sub-product is zero (the `0` factor at edge `b`
annihilates the product). -/
theorem submult_splitCut_eq_zero_of_cross (a e : Fin (N + 1)) (b : Fin N) {i j : Fin (N + 1)}
    (hij : i ≤ j) (hcross : i ≤ b.castSucc ∧ b.succ ≤ j) :
    submult (intervalDim a e) (splitCut (k := k) a e b) i j hij = 0 := by
  have hcr1v : (i : ℕ) ≤ (b : ℕ) := by
    have := hcross.1; rwa [Fin.le_def, Fin.val_castSucc] at this
  induction j using Fin.induction with
  | zero =>
    have hcr2 := hcross.2
    rw [Fin.le_def, Fin.val_succ, Fin.val_zero] at hcr2; omega
  | succ p ih =>
    have hcr2v : (b : ℕ) + 1 ≤ (p : ℕ) + 1 := by
      have := hcross.2; rwa [Fin.le_def, Fin.val_succ, Fin.val_succ] at this
    have hip : i ≤ p.castSucc := by
      rw [Fin.le_def, Fin.val_castSucc]; omega
    rw [submult_succ (intervalDim a e) (splitCut a e b) i p hip]
    by_cases hpb : p = b
    · -- the top edge is the cut: its `0` block kills the product
      subst hpb
      rw [splitCut_apply_self]
      exact Matrix.zero_mul _
    · -- the top edge is not the cut, but the path below still crosses
      have hpbv : (p : ℕ) ≠ (b : ℕ) := fun h ↦ hpb (Fin.val_injective h)
      have hsub : i ≤ b.castSucc ∧ b.succ ≤ p.castSucc := by
        refine ⟨hcross.1, ?_⟩
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      rw [ih hip hsub, Matrix.mul_zero]

/-- **The cut chain's rank pattern (indicator).** `r_{ij}(splitCut a e b) = 1` exactly when
`[i,j] ⊆ [a,e]` and the path does not cross the cut edge `b`. Equivalently the sum of the two
sub-interval indicators `[a ≤ i ∧ j ≤ b]` and `[b+1 ≤ i ∧ j ≤ e]` — the rank pattern of the split
downstairs `M_{[a,b]} ⊕ M_{[b+1,e]}`. -/
theorem rankPattern_splitCut [Nontrivial k] (a e : Fin (N + 1)) (b : Fin N) {i j : Fin (N + 1)}
    (hae : a ≤ b.castSucc) (hbe : b.succ ≤ e) (hij : i ≤ j) :
    rankPattern (intervalDim a e) (splitCut (k := k) a e b) i j hij
      = (if a ≤ i ∧ j ≤ b.castSucc then 1 else 0) + (if b.succ ≤ i ∧ j ≤ e then 1 else 0) := by
  rw [rankPattern]
  -- pin all order facts to `Fin.val` arithmetic
  have hbc : (b.castSucc : Fin (N + 1)).val = (b : ℕ) := Fin.val_castSucc b
  have hbs : (b.succ : Fin (N + 1)).val = (b : ℕ) + 1 := Fin.val_succ b
  have hijv : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
  have haev : (a : ℕ) ≤ (b : ℕ) := by have := Fin.le_def.mp hae; rwa [hbc] at this
  have hbev : (b : ℕ) + 1 ≤ (e : ℕ) := by have := Fin.le_def.mp hbe; rwa [hbs] at this
  -- the crossing predicate and the two containment indicators, all in `Fin.val`
  have hcrossv : (i ≤ b.castSucc ∧ b.succ ≤ j) ↔ ((i : ℕ) ≤ (b : ℕ) ∧ (b : ℕ) + 1 ≤ (j : ℕ)) := by
    rw [Fin.le_def, Fin.le_def, hbc, hbs]
  have hleftv : (a ≤ i ∧ j ≤ b.castSucc) ↔ ((a : ℕ) ≤ (i : ℕ) ∧ (j : ℕ) ≤ (b : ℕ)) := by
    rw [Fin.le_def, Fin.le_def, hbc]
  have hrightv : (b.succ ≤ i ∧ j ≤ e) ↔ ((b : ℕ) + 1 ≤ (i : ℕ) ∧ (j : ℕ) ≤ (e : ℕ)) := by
    rw [Fin.le_def, Fin.le_def, hbs]
  have hcontv : (a ≤ i ∧ j ≤ e) ↔ ((a : ℕ) ≤ (i : ℕ) ∧ (j : ℕ) ≤ (e : ℕ)) := by
    rw [Fin.le_def, Fin.le_def]
  by_cases hcross : i ≤ b.castSucc ∧ b.succ ≤ j
  · -- crossing: sub-product is `0`, rank `0`; both sub-interval indicators vanish
    rw [hcrossv] at hcross
    rw [submult_splitCut_eq_zero_of_cross a e b hij (hcrossv.mpr hcross), Matrix.rank_zero,
      if_neg (fun h ↦ by rw [hleftv] at h; omega), if_neg (fun h ↦ by rw [hrightv] at h; omega),
      add_zero]
  · -- not crossing: sub-product agrees with `M_{[a,e]}`'s
    rw [submult_splitCut_eq_of_not_cross a e b hij hcross]
    rw [show (submult (intervalDim a e) (intervalModule a e) i j hij).rank
        = rankPattern (intervalDim a e) (intervalModule (k := k) a e) i j hij from rfl,
      rankPattern_intervalModule]
    rw [hcrossv] at hcross
    by_cases hcont : a ≤ i ∧ j ≤ e
    · rw [if_pos hcont, hcontv] at *
      by_cases hL : (a : ℕ) ≤ (i : ℕ) ∧ (j : ℕ) ≤ (b : ℕ)
      · rw [if_pos (hleftv.mpr hL), if_neg (fun h ↦ by rw [hrightv] at h; omega)]
      · rw [if_neg (fun h ↦ hL (hleftv.mp h)), if_pos (hrightv.mpr (by omega)), zero_add]
    · rw [if_neg hcont, hcontv] at *
      rw [if_neg (fun h ↦ hcont ⟨(hleftv.mp h).1, by have := (hleftv.mp h).2; omega⟩),
        if_neg (fun h ↦ hcont ⟨by have := (hrightv.mp h).1; omega, (hrightv.mp h).2⟩), add_zero]

/-- The split downstairs dimension vector equals `M_{[a,e]}`'s: `[a,b] ⊔ [b+1,e]` partitions `[a,e]`
(for `a ≤ b` and `b+1 ≤ e`). -/
theorem foldDim_split_eq (a e : Fin (N + 1)) (b : Fin N) (hae : a ≤ b.castSucc)
    (hbe : b.succ ≤ e) :
    foldDim [(a, b.castSucc), (b.succ, e)] = intervalDim a e := by
  funext l
  have hbc : (b.castSucc : Fin (N + 1)).val = (b : ℕ) := Fin.val_castSucc b
  have hbs : (b.succ : Fin (N + 1)).val = (b : ℕ) + 1 := Fin.val_succ b
  have haev : (a : ℕ) ≤ (b : ℕ) := by have := Fin.le_def.mp hae; rwa [hbc] at this
  have hbev : (b : ℕ) + 1 ≤ (e : ℕ) := by have := Fin.le_def.mp hbe; rwa [hbs] at this
  -- the three `if` conditions in `Fin.val` terms
  have hL : (a ≤ l ∧ l ≤ b.castSucc) ↔ ((a : ℕ) ≤ (l : ℕ) ∧ (l : ℕ) ≤ (b : ℕ)) := by
    rw [Fin.le_def, Fin.le_def, hbc]
  have hR : (b.succ ≤ l ∧ l ≤ e) ↔ ((b : ℕ) + 1 ≤ (l : ℕ) ∧ (l : ℕ) ≤ (e : ℕ)) := by
    rw [Fin.le_def, Fin.le_def, hbs]
  have hC : (a ≤ l ∧ l ≤ e) ↔ ((a : ℕ) ≤ (l : ℕ) ∧ (l : ℕ) ≤ (e : ℕ)) := by
    rw [Fin.le_def, Fin.le_def]
  simp only [foldDim, intervalDim, add_zero]
  by_cases hC' : (a : ℕ) ≤ (l : ℕ) ∧ (l : ℕ) ≤ (e : ℕ)
  · rw [if_pos (hC.mpr hC')]
    by_cases hb' : (l : ℕ) ≤ (b : ℕ)
    · rw [if_pos (hL.mpr ⟨hC'.1, hb'⟩), if_neg (fun h ↦ by have := (hR.mp h).1; omega)]
    · rw [if_neg (fun h ↦ hb' (hL.mp h).2), if_pos (hR.mpr ⟨by omega, hC'.2⟩)]
  · rw [if_neg (fun h ↦ hC' (hC.mp h)),
      if_neg (fun h ↦ hC' ⟨(hL.mp h).1, by have := (hL.mp h).2; omega⟩),
      if_neg (fun h ↦ hC' ⟨by have := (hR.mp h).1; omega, (hR.mp h).2⟩)]

/-- **The cut chain realizes the split downstairs (orbit equivalence).** For `a ≤ b` and `b+1 ≤ e`
the cut chain `splitCut a e b` is `G_d`-equivalent to (a reindexing of) the genuine split downstairs
interval direct sum `M_{[a,b]} ⊕ M_{[b+1,e]}`: they have equal rank patterns
(`rankPattern_splitCut` matches `rankPattern_intervalDirectSum`), so by the complete invariant
`rankPattern_eq_iff_orbit` there is a base change between them. The split move thus genuinely
degenerates `M_{[a,e]}` to `M_{[a,b]} ⊕ M_{[b+1,e]}`. -/
theorem splitCut_orbit_intervalDirectSum (a e : Fin (N + 1)) (b : Fin N) (hae : a ≤ b.castSucc)
    (hbe : b.succ ≤ e) :
    ∃ P : BaseChangeGroup (k := k) (intervalDim a e),
      P • splitCut a e b
        = (foldDim_split_eq a e b hae hbe) ▸
            intervalDirectSum (k := k) [(a, b.castSucc), (b.succ, e)] := by
  set h := foldDim_split_eq a e b hae hbe with hh
  refine orbit_of_rankPattern_eq (splitCut a e b)
    (h ▸ intervalDirectSum (k := k) [(a, b.castSucc), (b.succ, e)]) (fun i j hij ↦ ?_)
  rw [rankPattern_splitCut a e b hae hbe hij, rankPattern_transport h
    (intervalDirectSum (k := k) [(a, b.castSucc), (b.succ, e)])]
  have hcast : (rankPattern (foldDim [(a, b.castSucc), (b.succ, e)])
      (intervalDirectSum (k := k) [(a, b.castSucc), (b.succ, e)]) i j hij : ℤ)
        = ((if a ≤ i ∧ j ≤ b.castSucc then 1 else 0)
          + (if b.succ ≤ i ∧ j ≤ e then 1 else 0) : ℕ) := by
    rw [rankPattern_intervalDirectSum, List.map_cons, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_cons, List.sum_nil, add_zero, rankPattern_intervalModule, rankPattern_intervalModule,
      Nat.cast_add, Nat.cast_ite, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact_mod_cast hcast.symm

section Witness

/-! ## Non-vacuity witnesses

`N = 2` (`Fin 3`), over `ℚ` (`Infinite`, not algebraically closed — the closure headlines use only
`Infinite`). The split move `M_{[0,2]} ⇝ M_{[0,0]} ⊕ M_{[1,2]}` (cut at edge `b = 0`): the cut chain
`splitCut 0 2 0` has its flattening in the closure of the orbit of `M_{[0,2]}`, and is
`G_d`-equivalent to the genuine split sum `M_{[0,0]} ⊕ M_{[1,2]}`. The common-summand lemma fires on
the certified `(1,2,1)` witness with a `1`-dimensional `rest`. -/

/-- The split move fires on `M_{[0,2]}` over `ℚ` (`Fin 3`, cut edge `b = 0`): the cut chain's
flattening lies in the Zariski closure of the orbit of `M_{[0,2]}`. -/
example : canonicalCoord (intervalDim (0 : Fin 3) 2) (splitCut (k := ℚ) 0 2 0)
    ∈ MvPolynomial.zeroLocus (σ := RepCoord (intervalDim (0 : Fin 3) 2)) (k := ℚ) ℚ
        (MvPolynomial.vanishingIdeal (σ := RepCoord (intervalDim (0 : Fin 3) 2)) (K := ℚ) ℚ
          (orbitSet (intervalModule 0 2))) :=
  splitCut_mem_closure 0 2 0

/-- The cut chain `splitCut 0 2 0` is `G_d`-equivalent to the genuine split sum `M_{[0,0]} ⊕
M_{[1,2]}` over `ℚ` — the split realization is non-vacuous on a concrete tuple. -/
example : ∃ P : BaseChangeGroup (k := ℚ) (intervalDim (0 : Fin 3) 2),
    P • splitCut 0 2 0
      = (foldDim_split_eq (0 : Fin 3) 2 0 (by decide) (by decide)) ▸
          intervalDirectSum (k := ℚ) [((0 : Fin 3), (0 : Fin 3)), (1, 2)] :=
  splitCut_orbit_intervalDirectSum 0 2 0 (by decide) (by decide)

/-- The common-summand lemma fires with the certified `(1,2,1)` witness `D₀ = M_{[0,1]} ⊕ M_{[1,2]}`
in the closure of `U₀ = M_{[0,2]} ⊕ M_{[1,1]}` (`boxMoveWitness…`), riding a `1`-dimensional summand
`R` (`M_{[0,0]}`): the flattening of `dirSum D₀ R` lies in the closure of `orbit (dirSum U₀ R)`. -/
example : canonicalCoord (fun l ↦ boxDim l + intervalDim (0 : Fin 3) 0 l)
      (dirSum boxMoveWitnessDown (intervalModule 0 0))
    ∈ MvPolynomial.zeroLocus
        (σ := RepCoord (fun l ↦ boxDim l + intervalDim (0 : Fin 3) 0 l)) (k := ℚ) ℚ
        (MvPolynomial.vanishingIdeal
          (σ := RepCoord (fun l ↦ boxDim l + intervalDim (0 : Fin 3) 0 l)) (K := ℚ) ℚ
          (orbitSet (dirSum boxMoveWitnessUp (intervalModule 0 0)))) :=
  mem_closure_dirSum_of_mem_closure boxMoveWitnessUp boxMoveWitnessDown (intervalModule 0 0)
    boxMoveWitnessFamilyPoly
    (by rw [tupleEval_boxMoveWitnessFamilyPoly, boxMoveWitnessFamily_zero])
    (fun t ht ↦ by rw [tupleEval_boxMoveWitnessFamilyPoly]; exact boxMoveWitnessFamily_mem_orbit ht)

end Witness

end DLNFibre.Core
