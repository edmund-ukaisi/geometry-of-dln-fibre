import DLNFibre.Core.BoxMoveDegeneration

/-!
# `DLNFibre.Core.BoxMoveGeneral` — the general box-move degeneration (L6.1-general)

Building blocks above the landed degeneration engine
`mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily`, generalising the certified `(1,2,1)`
witness of `DLNFibre.Core.BoxMoveDegeneration` towards the full box move (`a < c ≤ b+1 ≤ e`,
arbitrary `rest`):

* **Common-summand lemma** (`mem_closure_dirSum_of_mem_closure`): if the downstairs flattening of
  `D₀` lies in the Zariski closure of the orbit of `U₀` (via *any* polynomial family), then the same
  holds for `dirSum D₀ R`/`dirSum U₀ R` with a common block-diagonal summand `R`. The degeneration
  family is `dirSumPoly F₀ (const R)` (block-diagonal, `R` fixed) and the `t ≠ 0` base change is
  `P₀ ⊕ 1_R` (`liftDirSumBaseChange`: `P₀` on the first block, identity on the common `R`). This
  isolates `rest` from the symbolic two-interval move.

* **Downstairs transport** (`mem_closure_of_polynomialFamily_orbitEquiv`,
  `mem_closure_dirSum_of_mem_closure_orbitEquiv`): a constant base change `Q` carries the family
  (`smulPoly Q F`), letting the engine land an *orbit-equivalent* downstairs `D' = Q • D₀` — the
  bridge from a recombination limit (only `G_d`-equivalent to the genuine interval sum) to the list
  form.

* **Split box move, full §4 list headline** (`splitMove_intervalDirectSum_mem_closure`): the split
  case `c = b+1` with **arbitrary `rest`** — for `Lup = (a,e) :: rest`, `Ldn = (a,b) :: (b+1,e) :: rest`,
  `canonicalCoord (intervalDirectSum Ldn) ∈ closure (orbit (intervalDirectSum Lup))` (the two lists
  share a dimension vector; `Ldn` is transported onto it). The bare split-move pieces
  (`splitCut_mem_closure`, `splitCut_orbit_intervalDirectSum`) use the cut chain `splitCut a e b` and
  the explicit diagonal base change `splitBaseChange`.

* **Non-split box move (`a < c ≤ b < e`, dim-2 overlap on `[c,b]`) — SCAFFOLDING ONLY.** The
  recombination family `splice a c e b λ` (the upstairs `M_{[a,e]} ⊕ M_{[c,b]}` with the single edge
  `b` overwritten by the recombination row `[λ, 1]`, defined entrywise so it is dimension-agnostic),
  its off-edge agreement (`splice_apply_ne`), the sub-product concatenation (`submult_concat`), the
  two segment lemmas (`submult_splice_below` / `submult_splice_above`), and the **crossing
  factorization** `submult_splice_cross` (`submult (splice λ) i j = submult U₂ (b+1) j · (splice λ b)
  · submult U₂ i b` for `i ≤ b < j`) are landed. The **remaining gap** is the crossing-rank
  computation `rankPattern (splice λ) = rankPattern (upstairs)` (`λ ≠ 0`) / `= rankPattern
  (downstairs)` (`λ = 0`) — the rank of the crossing 3-fold product (`≤ 1` by the target dimension,
  `1`/`0` by the nonzero recombination entry) — and the engine application + list-gluing on top of
  it. The math is settled (the rank is `[a≤i∧j≤e]+[c≤i∧j≤b]` upstairs, `[a≤i∧j≤b]+[c≤i∧j≤e]`
  downstairs; sympy-certified, thread 22/24) and the route is verified; the residual is the heavy
  symbolic `Fin`-index entry computation (see the thread-27 card).

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

/-! ## Base change of a polynomial family and the downstairs-transport wrapper

A constant `k`-base change `Q` conjugates a polynomial-coefficient family entrywise (the unit matrices
mapped into `Polynomial k` by `C`), commuting with `eval`-at-`t`: `tupleEval (smulPoly Q F) t = Q •
tupleEval F t`. This lets the engine land an **orbit-equivalent** downstairs `D' = Q • D₀` (rather than
`D₀` itself) in the same closure — the bridge the list form needs (the genuine split sum is `G_d`-equivalent
to the cut chain via `splitCut_orbit_intervalDirectSum`, not equal to it). -/

/-- The base change `Q • F` of a polynomial-coefficient family `F`: the unit matrices `Q` mapped into
`Polynomial k` by `C` and conjugating each edge `F i = Q_{i+1} · F i · Q_i⁻¹`. -/
noncomputable def smulPoly {d : Fin (N + 1) → ℕ} (Q : BaseChangeGroup (k := k) d)
    (F : Tuple (k := Polynomial k) d) : Tuple (k := Polynomial k) d :=
  fun i ↦ (Units.val (Q i.succ)).map Polynomial.C * F i
    * (Units.val (Q i.castSucc)⁻¹).map Polynomial.C

/-- `tupleEval (smulPoly Q F) t = Q • tupleEval F t`: evaluation commutes with the constant base
change (`eval ∘ C = id`, `eval` a ring hom). -/
theorem tupleEval_smulPoly {d : Fin (N + 1) → ℕ} (Q : BaseChangeGroup (k := k) d)
    (F : Tuple (k := Polynomial k) d) (t : k) :
    tupleEval (smulPoly Q F) t = Q • tupleEval F t := by
  funext i
  rw [smul_eq_baseChange, baseChange_apply, tupleEval, smulPoly,
    show (Polynomial.eval t) = (Polynomial.evalRingHom t : Polynomial k → k) from
      (Polynomial.coe_evalRingHom t).symm,
    Matrix.map_mul, Matrix.map_mul]
  congr 1
  · congr 1
    funext r c
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  · funext r c
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]

/-- **The degeneration engine with downstairs transport.** Over an infinite field, if `F` has limit
`tupleEval F 0 = D₀`, every `t ≠ 0` point lies in the orbit of `U`, and `Q • D₀ = D'`, then the
flattening of the orbit-equivalent downstairs `D'` lies in the Zariski closure of the orbit of `U`.
The transported family is `smulPoly Q F` (limit `Q • D₀ = D'`; at `t ≠ 0`, `Q • (P • U) = (Q·P) • U`
still in the orbit of `U`). Lets a move whose limit is only `G_d`-equivalent to the target sum land
the target itself. -/
theorem mem_closure_of_polynomialFamily_orbitEquiv [Infinite k] {d : Fin (N + 1) → ℕ}
    (U D₀ D' : Tuple (k := k) d) (F : Tuple (k := Polynomial k) d) (Q : BaseChangeGroup (k := k) d)
    (h0 : tupleEval F 0 = D₀) (hQ : Q • D₀ = D')
    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U = tupleEval F t) :
    canonicalCoord d D'
      ∈ MvPolynomial.zeroLocus (σ := RepCoord d) (k := k) k
          (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U)) := by
  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily U D' (smulPoly Q F) ?_
    (fun t ht ↦ ?_)
  · rw [tupleEval_smulPoly, h0, hQ]
  · obtain ⟨P, hP⟩ := horb t ht
    refine ⟨Q * P, ?_⟩
    rw [mul_smul Q P U, hP, tupleEval_smulPoly]

/-- **Common-summand lemma with downstairs transport.** Combines the `rest` reduction with the
downstairs orbit-equivalence: if `F₀` degenerates `U₀ ⇝ D₀` and `Q • (dirSum D₀ R) = D'`, then the
flattening of the orbit-equivalent `D'` lies in the closure of the orbit of `dirSum U₀ R`. The
two-interval move lives in `D₀`, the appended `rest` rides as `R`, and `Q` carries the (cut-chain)
limit `dirSum D₀ R` onto the genuine interval direct sum `D'` — the form the list headline lands. -/
theorem mem_closure_dirSum_of_mem_closure_orbitEquiv [Infinite k] {d d' : Fin (N + 1) → ℕ}
    (U₀ D₀ : Tuple (k := k) d) (R : Tuple (k := k) d') (F₀ : Tuple (k := Polynomial k) d)
    (Q : BaseChangeGroup (k := k) (fun l ↦ d l + d' l)) (D' : Tuple (k := k) (fun l ↦ d l + d' l))
    (h0 : tupleEval F₀ 0 = D₀) (hQ : Q • dirSum D₀ R = D')
    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U₀ = tupleEval F₀ t) :
    canonicalCoord (fun l ↦ d l + d' l) D'
      ∈ MvPolynomial.zeroLocus (σ := RepCoord (fun l ↦ d l + d' l)) (k := k) k
          (MvPolynomial.vanishingIdeal (σ := RepCoord (fun l ↦ d l + d' l)) (K := k) k
            (orbitSet (dirSum U₀ R))) := by
  refine mem_closure_of_polynomialFamily_orbitEquiv (dirSum U₀ R) (dirSum D₀ R) D'
    (dirSumPoly F₀ (constPoly R)) Q ?_ hQ (fun t ht ↦ ?_)
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

/-! ## The split box move, glued into the §4 list headline (`Lup`/`Ldn`, arbitrary `rest`)

The full §4 statement for the split case `c = b+1`: with `Lup = (a,e) :: rest` and
`Ldn = (a, b.castSucc) :: (b.succ, e) :: rest`, the flattening of `intervalDirectSum Ldn`
(transported onto the common dimension vector `foldDim Lup`, since `foldDim Ldn = foldDim Lup`) lies
in the Zariski closure of the orbit of `intervalDirectSum Lup`. The two-interval move is `splitCut a
e b ⇝ M_{[a,b]} ⊕ M_{[b+1,e]}` (no `(c,b)` summand in the split case); `rest` rides as the common
summand `R = intervalDirectSum rest`; the downstairs `dirSum (splitCut a e b) R` is carried by a base
change onto `intervalDirectSum Ldn`. -/

/-- `foldDim` of the split-down list equals `foldDim` of the up list: `[a,b] ⊔ [b+1,e]` partitions
`[a,e]`, so `(a,bc) :: (bs,e) :: rest` and `(a,e) :: rest` have the same dimension vector. -/
theorem foldDim_splitCons_eq (a e : Fin (N + 1)) (b : Fin N) (rest : List (Fin (N + 1) × Fin (N + 1)))
    (hae : a ≤ b.castSucc) (hbe : b.succ ≤ e) :
    foldDim ((a, b.castSucc) :: (b.succ, e) :: rest)
      = (fun l ↦ intervalDim a e l + foldDim rest l) := by
  funext l
  have := congrFun (foldDim_split_eq (N := N) a e b hae hbe) l
  simp only [foldDim, add_zero] at this ⊢
  omega

/-- **The split downstairs sum is `G_d`-equivalent to `dirSum (splitCut a e b) rest`.** For a genuine
split (`a ≤ b`, `b+1 ≤ e`) the cut chain riding `rest` is carried by a base change onto the genuine
interval direct sum `M_{[a,b]} ⊕ M_{[b+1,e]} ⊕ rest` (transported onto the up dimension vector): equal
rank patterns (`rankPattern_splitCut` + block additivity = the `Ldn` cumul), then the complete
invariant `orbit_of_rankPattern_eq`. -/
theorem orbit_dirSum_splitCut_intervalDirectSum (a e : Fin (N + 1)) (b : Fin N)
    (rest : List (Fin (N + 1) × Fin (N + 1))) (hae : a ≤ b.castSucc) (hbe : b.succ ≤ e) :
    ∃ Q : BaseChangeGroup (k := k) (fun l ↦ intervalDim a e l + foldDim rest l),
      Q • dirSum (splitCut (k := k) a e b) (intervalDirectSum rest)
        = (foldDim_splitCons_eq a e b rest hae hbe) ▸
            intervalDirectSum (k := k) ((a, b.castSucc) :: (b.succ, e) :: rest) := by
  refine orbit_of_rankPattern_eq _ _ (fun i j hij ↦ ?_)
  rw [rankPattern_dirSum, rankPattern_splitCut a e b hae hbe hij,
    rankPattern_transport (foldDim_splitCons_eq a e b rest hae hbe),
    rankPattern_intervalDirectSum (K := k) ((a, b.castSucc) :: (b.succ, e) :: rest),
    List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
    rankPattern_intervalModule, rankPattern_intervalModule,
    ← rankPattern_intervalDirectSum (K := k) rest]
  ring

/-- **The split box move, full §4 list headline (split case `c = b+1`).** Over an infinite field, for
a genuine split (`a ≤ b.castSucc`, `b.succ ≤ e`) and arbitrary `rest`, the flattening of
`intervalDirectSum ((a, b.castSucc) :: (b.succ, e) :: rest)` — the downstairs `Ldn`, transported onto
the common dimension vector `foldDim ((a,e) :: rest)` (the lists share a dimension vector) — lies in
the Zariski closure of the orbit of `intervalDirectSum ((a, e) :: rest)`, the upstairs `Lup`. This is
the §4 headline for the split case: `Lup = (a,e) :: rest`, `Ldn = (a,b) :: (b+1,e) :: rest`. The
common-summand lemma rides `rest` as `R`; the split family `splitFamilyPoly` degenerates `M_{[a,e]}`
to the cut chain; the base change `orbit_dirSum_splitCut_intervalDirectSum` carries the cut-chain limit
onto the genuine interval direct sum. -/
theorem splitMove_intervalDirectSum_mem_closure [Infinite k] (a e : Fin (N + 1)) (b : Fin N)
    (rest : List (Fin (N + 1) × Fin (N + 1))) (hae : a ≤ b.castSucc) (hbe : b.succ ≤ e) :
    canonicalCoord (fun l ↦ intervalDim a e l + foldDim rest l)
        ((foldDim_splitCons_eq a e b rest hae hbe) ▸
          intervalDirectSum (k := k) ((a, b.castSucc) :: (b.succ, e) :: rest))
      ∈ MvPolynomial.zeroLocus (σ := RepCoord (fun l ↦ intervalDim a e l + foldDim rest l))
          (k := k) k
          (MvPolynomial.vanishingIdeal
            (σ := RepCoord (fun l ↦ intervalDim a e l + foldDim rest l)) (K := k) k
            (orbitSet (dirSum (intervalModule a e) (intervalDirectSum rest)))) := by
  obtain ⟨Q, hQ⟩ := orbit_dirSum_splitCut_intervalDirectSum (k := k) a e b rest hae hbe
  exact mem_closure_dirSum_of_mem_closure_orbitEquiv (intervalModule a e) (splitCut a e b)
    (intervalDirectSum rest) (splitFamilyPoly a e b) Q _
    (tupleEval_splitFamilyPoly_zero a e b) hQ
    (fun t ht ↦ tupleEval_splitFamilyPoly_mem_orbit a e b ht)

/-! ## The non-split box move `M_{[a,e]} ⊕ M_{[c,b]} ⇝ M_{[a,b]} ⊕ M_{[c,e]}` (`a < c ≤ b < e`)

The genuine two-strand recombination, dim-2 overlap on `[c,b]`. Over the **upstairs** dimension vector
`d₂ = intervalDim a e + intervalDim c b` (`b` here the vertex `b.castSucc`), the upstairs is `U₂ =
M_{[a,e]} ⊕ M_{[c,b]}` (block-diagonal). The family `splice a c e b λ` edits `U₂` at the single
recombination edge `b → b+1`: there the source vertex carries both strands (long `[a,e]`, short
`[c,b]`) and the target only the long, so the edge is the `1×2` row `[λ, 1]` in (long, short) source
coordinates (`finSumFinEquiv` reads the strand). At `λ = 0` the row is `[0, 1]` — the downstairs
recombination (kill the long strand, route the short through); at `λ ≠ 0` it has the upstairs rank
pattern. Off edge `b` it is `U₂` (block-diagonal). The `t ≠ 0` orbit membership uses the **complete
invariant** `orbit_of_rankPattern_eq` (the lighter route at symbolic indices): we show `rankPattern
(splice … t) = rankPattern U₂` for `t ≠ 0`, no explicit `P(t)` entrywise. -/

/-- General sub-product concatenation: `submult i j = submult m j · submult i m` for `i ≤ m ≤ j`.
Telescopes the product at any interior vertex `m`; the matrix-side splitter for crossing arguments. -/
theorem submult_concat (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i m j : Fin (N + 1))
    (him : i ≤ m) (hmj : m ≤ j) :
    submult d A i j (him.trans hmj) = submult d A m j hmj * submult d A i m him := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : m = 0 := Fin.le_zero_iff.mp hmj
    obtain rfl : i = 0 := Fin.le_zero_iff.mp him
    rw [submult_self, Matrix.mul_one]
  | succ p ih =>
    rcases eq_or_lt_of_le hmj with heq | hlt
    · subst heq; rw [submult_self, Matrix.one_mul]
    · have hmp : m ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      have hip : i ≤ p.castSucc := him.trans hmp
      rw [submult_succ d A i p hip, submult_succ d A m p hmp, ih hmp, Matrix.mul_assoc]

/-- The **recombination family** `splice a c e b λ : Tuple (intervalDim a e + intervalDim c b)`: the
upstairs `M_{[a,e]} ⊕ M_{[c,b]}` with the single edge `b` overwritten by the recombination row — the
long strand (`finSumFinEquiv inl`) carries `λ`, the short strand (`inr`) carries `1`. Defined entrywise
(scalar-level branch on the edge), so it is dimension-agnostic: no `fromBlocks`/`▸` at the edge. -/
noncomputable def splice (a c e : Fin (N + 1)) (b : Fin N) (lam : k) :
    Tuple (k := k) (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) :=
  fun p r s ↦ if p = b
    then (match finSumFinEquiv.symm s with | Sum.inl _ => lam | Sum.inr _ => 1)
    else dirSum (intervalModule a e) (intervalModule c b.castSucc) p r s

/-- `splice` agrees with the upstairs `U₂ = M_{[a,e]} ⊕ M_{[c,b]}` off the recombination edge `b`. -/
theorem splice_apply_ne (a c e : Fin (N + 1)) (b : Fin N) (lam : k) {p : Fin N} (hp : p ≠ b) :
    splice (k := k) a c e b lam p
      = dirSum (intervalModule a e) (intervalModule c b.castSucc) p := by
  funext r s; rw [splice, if_neg hp]

/-- Below the recombination edge (`j ≤ b`), the splice sub-product equals the upstairs `U₂`'s — the
path stays off edge `b` (every top factor is at `p < b`). -/
theorem submult_splice_below (a c e : Fin (N + 1)) (b : Fin N) (lam : k) {i j : Fin (N + 1)}
    (hij : i ≤ j) (hjb : j ≤ b.castSucc) :
    submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (splice (k := k) a c e b lam) i j hij
      = submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
          (dirSum (intervalModule a e) (intervalModule c b.castSucc)) i j hij := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := Fin.le_zero_iff.mp hij
    rw [submult_self, submult_self]
  | succ p ih =>
    rcases eq_or_lt_of_le hij with heq | hlt
    · obtain rfl := heq; rw [submult_self, submult_self]
    · have hip : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      have hjbv : (p : ℕ) + 1 ≤ (b : ℕ) := by
        have := Fin.le_def.mp hjb; rw [Fin.val_succ, Fin.val_castSucc] at this; exact this
      have hpb : p ≠ b := fun h ↦ by rw [h] at hjbv; omega
      have hpbcs : p.castSucc ≤ b.castSucc := by
        rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc]; omega
      rw [submult_succ _ (splice a c e b lam) i p hip, submult_succ _ (dirSum _ _) i p hip,
          ih hip hpbcs, splice_apply_ne a c e b lam hpb]

/-- Above the recombination edge (`b+1 ≤ i`), the splice sub-product equals the upstairs `U₂`'s — the
path stays off edge `b` (every top factor is at `p > b`). -/
theorem submult_splice_above (a c e : Fin (N + 1)) (b : Fin N) (lam : k) {i j : Fin (N + 1)}
    (hij : i ≤ j) (hbi : b.succ ≤ i) :
    submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (splice (k := k) a c e b lam) i j hij
      = submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
          (dirSum (intervalModule a e) (intervalModule c b.castSucc)) i j hij := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := Fin.le_zero_iff.mp hij
    rw [submult_self, submult_self]
  | succ p ih =>
    rcases eq_or_lt_of_le hij with heq | hlt
    · obtain rfl := heq; rw [submult_self, submult_self]
    · have hip : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      have hbiv : (b : ℕ) + 1 ≤ (i : ℕ) := by
        have := Fin.le_def.mp hbi; rw [Fin.val_succ] at this; exact this
      have hipv : (i : ℕ) ≤ (p : ℕ) := by
        have := Fin.le_def.mp hip; rw [Fin.val_castSucc] at this; exact this
      have hpb : p ≠ b := fun h ↦ by rw [h] at hipv; omega
      rw [submult_succ _ (splice a c e b lam) i p hip, submult_succ _ (dirSum _ _) i p hip,
          ih hip, splice_apply_ne a c e b lam hpb]

/-- **Crossing factorization.** For `i ≤ b` and `b+1 ≤ j` the splice sub-product factors through the
single recombination edge: `submult (splice λ) i j = submult U₂ (b+1) j · (splice λ b) · submult U₂ i
b`, the two segments being upstairs sub-products (off edge `b`). -/
theorem submult_splice_cross (a c e : Fin (N + 1)) (b : Fin N) (lam : k) {i j : Fin (N + 1)}
    (hib : i ≤ b.castSucc) (hbj : b.succ ≤ j) :
    submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (splice (k := k) a c e b lam) i j ((hib.trans (Fin.castSucc_le_succ b)).trans hbj)
      = submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
          (dirSum (intervalModule a e) (intervalModule c b.castSucc)) b.succ j hbj
        * splice a c e b lam b
        * submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
            (dirSum (intervalModule a e) (intervalModule c b.castSucc)) i b.castSucc hib := by
  rw [submult_concat _ _ i b.succ j (hib.trans (Fin.castSucc_le_succ b)) hbj,
    submult_splice_above a c e b lam (i := b.succ) (j := j) hbj le_rfl,
    submult_succ _ (splice a c e b lam) i b hib,
    submult_splice_below a c e b lam (i := i) (j := b.castSucc) hib le_rfl, Matrix.mul_assoc]

/-! ## Rank brick lemmas (over a field) and block-matrix entry access -/

/-- Over a field, a matrix of rank `0` is the zero matrix (its column span is `⊥`). -/
theorem matrix_eq_zero_of_rank_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n k) (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank_eq_finrank_span_cols] at h
  have hbot : Submodule.span k (Set.range A.col) = ⊥ := by
    rw [Submodule.finrank_eq_zero] at h; exact h
  rw [Submodule.span_eq_bot] at hbot
  funext i j
  have := congrFun (hbot _ ⟨j, rfl⟩) i
  simpa [Matrix.col] using this

/-- Over a field, a nonzero matrix has rank `≥ 1` (contrapositive of
`matrix_eq_zero_of_rank_eq_zero`). -/
theorem one_le_rank_of_ne_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n k) (h : A ≠ 0) : 1 ≤ A.rank := by
  rcases Nat.eq_zero_or_pos A.rank with hr | hr
  · exact absurd (matrix_eq_zero_of_rank_eq_zero A hr) h
  · exact hr

/-- Long–long entry of a reindexed block-diagonal: `(bd A B)(inl r)(inl s) = A r s`. -/
theorem reindex_fromBlocks_inl_inl {a₁ a₂ b₁ b₂ : ℕ} (A : Matrix (Fin a₁) (Fin b₁) k)
    (B : Matrix (Fin a₂) (Fin b₂) k) (r : Fin a₁) (s : Fin b₁) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
      (finSumFinEquiv (Sum.inl r)) (finSumFinEquiv (Sum.inl s)) = A r s := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

/-- Short–short entry of a reindexed block-diagonal: `(bd A B)(inr r)(inr s) = B r s`. -/
theorem reindex_fromBlocks_inr_inr {a₁ a₂ b₁ b₂ : ℕ} (A : Matrix (Fin a₁) (Fin b₁) k)
    (B : Matrix (Fin a₂) (Fin b₂) k) (r : Fin a₂) (s : Fin b₂) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
      (finSumFinEquiv (Sum.inr r)) (finSumFinEquiv (Sum.inr s)) = B r s := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

/-- Long–short (off-diagonal) entry of a reindexed block-diagonal is `0`. -/
theorem reindex_fromBlocks_inl_inr {a₁ a₂ b₁ b₂ : ℕ} (A : Matrix (Fin a₁) (Fin b₁) k)
    (B : Matrix (Fin a₂) (Fin b₂) k) (r : Fin a₁) (s : Fin b₂) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
      (finSumFinEquiv (Sum.inl r)) (finSumFinEquiv (Sum.inr s)) = 0 := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

/-- Short–long (off-diagonal) entry of a reindexed block-diagonal is `0`. -/
theorem reindex_fromBlocks_inr_inl {a₁ a₂ b₁ b₂ : ℕ} (A : Matrix (Fin a₁) (Fin b₁) k)
    (B : Matrix (Fin a₂) (Fin b₂) k) (r : Fin a₂) (s : Fin b₁) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
      (finSumFinEquiv (Sum.inr r)) (finSumFinEquiv (Sum.inl s)) = 0 := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The recombination edge on the long source strand carries `λ` (depends only on the column). -/
theorem splice_edge_inl (a c e : Fin (N + 1)) (b : Fin N) (lam : k)
    (r : Fin ((fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) b.succ))
    (s : Fin (intervalDim a e b.castSucc)) :
    splice (k := k) a c e b lam b r (finSumFinEquiv (Sum.inl s)) = lam := by
  rw [splice, if_pos rfl, Equiv.symm_apply_apply]

/-- The recombination edge on the short source strand carries `1` (depends only on the column). -/
theorem splice_edge_inr (a c e : Fin (N + 1)) (b : Fin N) (lam : k)
    (r : Fin ((fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) b.succ))
    (s : Fin (intervalDim c b.castSucc b.castSucc)) :
    splice (k := k) a c e b lam b r (finSumFinEquiv (Sum.inr s)) = 1 := by
  rw [splice, if_pos rfl, Equiv.symm_apply_apply]

/-! ## The crossing rank: the four entry/zero cases and the master `if`-formula

For `i ≤ b.castSucc < b.succ ≤ j` the crossing product `above · recomb · below` (`submult_splice_cross`)
has at most one row (the long target at `j`, since the short strand is `0`-dimensional past
`b.castSucc`), so its rank is `≤ 1`. It is nonzero exactly when `j ≤ e` (the long target survives) and
the recombination row reaches a nonzero column — the short strand (`c ≤ i`, value `1`) or the long
strand (`a ≤ i` with `λ ≠ 0`). The two nonzero cases exhibit a witness entry; the two zero cases show
`recomb · below = 0`. -/

/-- Crossing nonzero, short strand (`c ≤ i`, `j ≤ e`): the witness entry `(long j, short i)` is `1`. -/
theorem splice_cross_ne_zero_short (a c e : Fin (N + 1)) (b : Fin N) (lam : k) {i j : Fin (N + 1)}
    (hac : a < c) (hcb : c ≤ b.castSucc) (hbe : b.succ ≤ e)
    (hib : i ≤ b.castSucc) (hbj : b.succ ≤ j)
    (hci : c ≤ i) (hje : j ≤ e) :
    (submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) b.succ j hbj
      * splice (k := k) a c e b lam b
      * submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
          (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) i b.castSucc hib)
        ≠ 0 := by
  have hae_bs : a ≤ b.succ := le_trans (le_of_lt (lt_of_lt_of_le hac hcb)) (Fin.castSucc_le_succ b)
  have hdimj : intervalDim a e j = 1 := intervalDim_eq_one ⟨le_trans hae_bs hbj, hje⟩
  have hdimi_short : intervalDim c b.castSucc i = 1 := intervalDim_eq_one ⟨hci, hib⟩
  have hdimbs_long : intervalDim a e b.succ = 1 := intervalDim_eq_one ⟨hae_bs, le_trans hbj hje⟩
  have hdimbc_short : intervalDim c b.castSucc b.castSucc = 1 := intervalDim_eq_one ⟨hcb, le_rfl⟩
  set r₀ : Fin ((fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) j) :=
    finSumFinEquiv (Sum.inl (Fin.cast hdimj.symm 0)) with hr₀
  set s₀ : Fin ((fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) i) :=
    finSumFinEquiv (Sum.inr (Fin.cast hdimi_short.symm 0)) with hs₀
  intro hzero
  have hentry := congrFun (congrFun hzero r₀) s₀
  rw [Matrix.zero_apply, submult_dirSum, submult_dirSum,
    submult_intervalModule_subset a e hbj hae_bs hje,
    submult_intervalModule_subset c b.castSucc hib hci le_rfl] at hentry
  rw [Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type] at hentry
  simp only [hr₀, hs₀, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type,
    reindex_fromBlocks_inl_inl, reindex_fromBlocks_inl_inr, reindex_fromBlocks_inr_inl,
    reindex_fromBlocks_inr_inr, splice_edge_inl, splice_edge_inr,
    Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hentry
  rw [hdimbc_short, hdimbs_long] at hentry
  simp at hentry

/-- Crossing nonzero, long strand (`λ ≠ 0`, `a ≤ i`, `j ≤ e`): the entry `(long j, long i)` is `λ`. -/
theorem splice_cross_ne_zero_long (a c e : Fin (N + 1)) (b : Fin N) (lam : k) {i j : Fin (N + 1)}
    (hac : a < c) (hcb : c ≤ b.castSucc) (hbe : b.succ ≤ e)
    (hib : i ≤ b.castSucc) (hbj : b.succ ≤ j)
    (hlam : lam ≠ 0) (hai : a ≤ i) (hje : j ≤ e) :
    (submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) b.succ j hbj
      * splice (k := k) a c e b lam b
      * submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
          (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) i b.castSucc hib)
        ≠ 0 := by
  have hae_bs : a ≤ b.succ := le_trans (le_of_lt (lt_of_lt_of_le hac hcb)) (Fin.castSucc_le_succ b)
  have hdimj : intervalDim a e j = 1 := intervalDim_eq_one ⟨le_trans hae_bs hbj, hje⟩
  have hbce : b.castSucc ≤ e := le_trans (Fin.castSucc_le_succ b) hbe
  have hdimi_long : intervalDim a e i = 1 := intervalDim_eq_one ⟨hai, le_trans hib hbce⟩
  have hdimbs_long : intervalDim a e b.succ = 1 := intervalDim_eq_one ⟨hae_bs, le_trans hbj hje⟩
  have hdimbc_long : intervalDim a e b.castSucc = 1 := intervalDim_eq_one ⟨le_trans hai hib, hbce⟩
  set r₀ : Fin ((fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) j) :=
    finSumFinEquiv (Sum.inl (Fin.cast hdimj.symm 0)) with hr₀
  set s₀ : Fin ((fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) i) :=
    finSumFinEquiv (Sum.inl (Fin.cast hdimi_long.symm 0)) with hs₀
  intro hzero
  have hentry := congrFun (congrFun hzero r₀) s₀
  rw [Matrix.zero_apply, submult_dirSum, submult_dirSum,
    submult_intervalModule_subset a e hbj hae_bs hje,
    submult_intervalModule_subset a e hib hai hbce] at hentry
  rw [Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type] at hentry
  simp only [hr₀, hs₀, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type,
    reindex_fromBlocks_inl_inl, reindex_fromBlocks_inl_inr, reindex_fromBlocks_inr_inl,
    reindex_fromBlocks_inr_inr, splice_edge_inl, splice_edge_inr,
    Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hentry
  rw [hdimbs_long, hdimbc_long] at hentry
  simp at hentry
  exact hlam hentry

/-- Crossing zero, `λ = 0` strand killed and `¬ c ≤ i` (short column absent): `recomb · below = 0`. -/
theorem splice_recomb_below_zero_of_lam_zero (a c e : Fin (N + 1)) (b : Fin N)
    {i j : Fin (N + 1)} (hib : i ≤ b.castSucc) (hbj : b.succ ≤ j) (hnc : ¬ c ≤ i) :
    splice (k := k) a c e b 0 b
      * submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
          (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) i b.castSucc hib
        = 0 := by
  have hdimi_short : intervalDim c b.castSucc i = 0 := intervalDim_eq_zero (fun h ↦ hnc h.1)
  rw [submult_dirSum]
  funext r s
  rw [Matrix.zero_apply, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  haveI : IsEmpty (Fin (intervalDim c b.castSucc i)) := by rw [hdimi_short]; infer_instance
  simp only [splice_edge_inl, splice_edge_inr, zero_mul, one_mul,
    reindex_fromBlocks_inl_inl, reindex_fromBlocks_inl_inr, reindex_fromBlocks_inr_inl,
    reindex_fromBlocks_inr_inr, Finset.sum_const_zero, add_zero, zero_add]
  refine Finset.sum_eq_zero (fun x _ ↦ ?_)
  obtain ⟨s', rfl⟩ := finSumFinEquiv.surjective s
  rcases s' with sl | sr
  · rw [reindex_fromBlocks_inr_inl]
  · exact (‹IsEmpty (Fin (intervalDim c b.castSucc i))›.elim sr)

/-- Crossing zero, both columns absent (`¬ a ≤ i`, `¬ c ≤ i`): the source dimension at `i` is `0`. -/
theorem splice_recomb_below_zero_of_no_long (a c e : Fin (N + 1)) (b : Fin N) (lam : k)
    {i j : Fin (N + 1)} (hib : i ≤ b.castSucc) (hbj : b.succ ≤ j) (hnc : ¬ c ≤ i) (hna : ¬ a ≤ i) :
    splice (k := k) a c e b lam b
      * submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
          (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) i b.castSucc hib
        = 0 := by
  have hdimi_short : intervalDim c b.castSucc i = 0 := intervalDim_eq_zero (fun h ↦ hnc h.1)
  have hdimi_long : intervalDim a e i = 0 := intervalDim_eq_zero (fun h ↦ hna h.1)
  funext r s
  have hd0 : (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) i = 0 := by
    simp only [hdimi_long, hdimi_short]
  haveI : IsEmpty (Fin ((fun l ↦ intervalDim a e l + intervalDim c b.castSucc l) i)) := by
    rw [hd0]; infer_instance
  exact this.elim s

open scoped Classical in
/-- **The crossing rank pattern.** For `i ≤ b.castSucc < b.succ ≤ j` (non-split regime
`a < c ≤ b.castSucc`, `b.succ ≤ e`): `r_{ij}(splice λ) = 1` iff `j ≤ e` and the recombination row
reaches a nonzero column (`(λ ≠ 0 ∧ a ≤ i) ∨ c ≤ i`), else `0`. The crossing block has `≤ 1` row, so
rank `≤ [j ≤ e]` (upper bound via `rankPattern_dirSum`); the nonzero/zero split is the four cases. -/
theorem rankPattern_splice_cross (a c e : Fin (N + 1)) (b : Fin N) (lam : k) {i j : Fin (N + 1)}
    (hac : a < c) (hcb : c ≤ b.castSucc) (hbe : b.succ ≤ e)
    (hib : i ≤ b.castSucc) (hbj : b.succ ≤ j) :
    rankPattern (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (splice (k := k) a c e b lam) i j ((hib.trans (Fin.castSucc_le_succ b)).trans hbj)
      = if j ≤ e ∧ ((lam ≠ 0 ∧ a ≤ i) ∨ c ≤ i) then 1 else 0 := by
  classical
  rw [rankPattern, submult_splice_cross a c e b lam hib hbj]
  set M := submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
      (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) b.succ j hbj
    * splice a c e b lam b
    * submult (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) i b.castSucc hib with hM
  have hae_bs : a ≤ b.succ := le_trans (le_of_lt (lt_of_lt_of_le hac hcb)) (Fin.castSucc_le_succ b)
  have hbcj : b.castSucc < j := lt_of_lt_of_le b.castSucc_lt_succ hbj
  have hub : M.rank ≤ (if j ≤ e then 1 else 0) := by
    have hle : M.rank ≤ rankPattern (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l)
        (dirSum (intervalModule (k := k) a e) (intervalModule c b.castSucc)) b.succ j hbj := by
      rw [hM, rankPattern, Matrix.mul_assoc]
      apply Matrix.rank_mul_le_left
    rw [rankPattern_dirSum, rankPattern_intervalModule, rankPattern_intervalModule] at hle
    have hsnd : ¬ (c ≤ b.succ ∧ j ≤ b.castSucc) := fun h ↦ absurd (lt_of_lt_of_le hbcj h.2)
      (lt_irrefl (b.castSucc : Fin (N + 1)))
    rw [if_neg hsnd, add_zero] at hle
    by_cases hje : j ≤ e
    · rw [if_pos ⟨hae_bs, hje⟩] at hle; rw [if_pos hje]; exact hle
    · rw [if_neg (fun h ↦ hje h.2)] at hle; rw [if_neg hje]; exact hle
  by_cases hcond : j ≤ e ∧ ((lam ≠ 0 ∧ a ≤ i) ∨ c ≤ i)
  · rw [if_pos hcond]
    obtain ⟨hje, hor⟩ := hcond
    refine le_antisymm (by rw [if_pos hje] at hub; exact hub) ?_
    rcases hor with ⟨hlam, hai⟩ | hci
    · refine one_le_rank_of_ne_zero M ?_
      rw [hM]
      exact splice_cross_ne_zero_long a c e b lam hac hcb hbe hib hbj hlam hai hje
    · refine one_le_rank_of_ne_zero M ?_
      rw [hM]
      exact splice_cross_ne_zero_short a c e b lam hac hcb hbe hib hbj hci hje
  · rw [if_neg hcond]
    by_cases hje : j ≤ e
    · have hcond' : ¬ ((lam ≠ 0 ∧ a ≤ i) ∨ c ≤ i) := fun h ↦ hcond ⟨hje, h⟩
      have hnc : ¬ c ≤ i := fun h ↦ hcond' (Or.inr h)
      have hla : lam = 0 ∨ ¬ a ≤ i := by
        by_cases hlam : lam = 0
        · exact Or.inl hlam
        · exact Or.inr (fun hai ↦ hcond' (Or.inl ⟨hlam, hai⟩))
      have hMzero : M = 0 := by
        rw [hM, Matrix.mul_assoc]
        rcases hla with rfl | hna
        · rw [splice_recomb_below_zero_of_lam_zero a c e b hib hbj hnc, Matrix.mul_zero]
        · rw [splice_recomb_below_zero_of_no_long a c e b lam hib hbj hnc hna, Matrix.mul_zero]
      rw [hMzero, Matrix.rank_zero]
    · rw [if_neg hje] at hub
      exact Nat.le_zero.mp hub

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

/-- The split move's **full §4 list headline** fires over `ℚ` with a `1`-dimensional `rest`
(`M_{[1,2]}`): `M_{[0,0]} ⊕ M_{[1,1]} ⊕ M_{[1,2]}` (the downstairs `Ldn = (0,0) :: (1,1) :: [(1,2)]`)
lies in the closure of the orbit of `M_{[0,1]} ⊕ M_{[1,2]}` (the upstairs `Lup = (0,1) :: [(1,2)]`),
cut at edge `b = 0`. -/
example :
    canonicalCoord (fun l ↦ intervalDim (0 : Fin 3) 1 l + foldDim [((1 : Fin 3), (2 : Fin 3))] l)
      ((foldDim_splitCons_eq (0 : Fin 3) 1 0 [((1 : Fin 3), (2 : Fin 3))] (by decide) (by decide)) ▸
        intervalDirectSum (k := ℚ) [((0 : Fin 3), (0 : Fin 3)), (1, 1), (1, 2)])
    ∈ MvPolynomial.zeroLocus
        (σ := RepCoord (fun l ↦ intervalDim (0 : Fin 3) 1 l + foldDim [((1 : Fin 3), (2 : Fin 3))] l))
        (k := ℚ) ℚ
        (MvPolynomial.vanishingIdeal
          (σ := RepCoord (fun l ↦ intervalDim (0 : Fin 3) 1 l + foldDim [((1 : Fin 3), (2 : Fin 3))] l))
          (K := ℚ) ℚ
          (orbitSet (dirSum (intervalModule 0 1) (intervalDirectSum [((1 : Fin 3), (2 : Fin 3))])))) :=
  splitMove_intervalDirectSum_mem_closure 0 1 0 [((1 : Fin 3), (2 : Fin 3))] (by decide) (by decide)

/-! ### Non-split scaffolding sanity (orientation against the certified `(1,2,1)` witness)

The non-split `splice` for `a = 0, c = 1, b = 1, e = 2` (`[c,b] = [1,1]`, the smallest genuine overlap)
has the witness dimension vector `(1,2,1)` and the recombination row `[λ, 1]` — matching the certified
`boxMoveWitnessFamily` edge `[t, 1]`. Confirms the scaffolding is the right object; the residual is the
crossing-rank computation. -/

/-- The non-split `splice` over `Fin 3` (`a=0, c=1, b=1, e=2`) has the `(1,2,1)` dimension vector. -/
example : (fun l ↦ intervalDim (0 : Fin 3) 2 l + intervalDim 1 (1 : Fin 3) l) = ![1, 2, 1] := by
  funext l; fin_cases l <;> decide

/-- The recombination edge of `splice 0 1 2 1 λ` reads the long strand (`inl`) as `λ` — the `[λ, 1]`
row that matches the certified witness's `[t, 1]` cut arrow. -/
example (lam : ℚ)
    (r : Fin ((fun l ↦ intervalDim (0 : Fin 3) 2 l + intervalDim 1 1 l) (1 : Fin 2).succ))
    (s' : Fin (intervalDim (0 : Fin 3) 2 (1 : Fin 2).castSucc)) :
    splice (k := ℚ) 0 1 2 1 lam 1 r (finSumFinEquiv (Sum.inl s')) = lam := by
  rw [splice, if_pos rfl, Equiv.symm_apply_apply]

end Witness

end DLNFibre.Core
