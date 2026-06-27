import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanRate
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet

/-!
# `RouteMBoundaryCleanU` — the clean-chart unit `U ≢ 0` a.e. (WALL 2, positivity leg)

The `NodeAchieverChart.Ubound` positivity for the clean radial chart: `U(u) := dlnLoss M 0
(unblownParams u)` is `> 0` a.e. on every box `[0,δ]^N`. Route (Codex-corroborated): `U = eval u
UPolyClean` for an explicit nonzero `MvPolynomial`, so `{U = 0}` is Lebesgue-null
(`MvPolynomial.ae_eval_ne_zero`, the banked `Core.MeasureTheory.PolynomialZeroSet`).

`UPolyClean` is the sum-of-squares of a coefficient-polymorphic matrix chain product `cprod` of the
polynomial parameter tuple (`X c` free, `C 1` pivot slot); `eval u` pushes through (`cprod_map`: the
chain product commutes with a ring hom's `Matrix.map`). It is nonzero because at the all-ones point
`u₁ ≡ 1` every entry of `unblownParams u₁` is `1` (the pivot if-branch is also `1`), so `prod M (allOnes)`
has `(0,0)` entry `= ∏ inner widths > 0` (widths positive on the rank-carrying chain), hence
`U(u₁) ≥ (prod 0 0)² > 0`.
-/

open scoped BigOperators
open Matrix MeasureTheory MvPolynomial

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## A coefficient-polymorphic matrix chain product (`cprod`) + its `ℝ`-link and `map` naturality

`prod`/`prodAux` are hardcoded to `ℝ`. `cprod` mirrors `prodAux` over any `CommRing`, so the polynomial
unit can be built over `MvPolynomial (Fin N) ℝ` and pushed back by `eval`. -/

/-- The coefficient-polymorphic chain product `A⁽⁰⁾·…·A⁽ᵏ⁻¹⁾` (mirrors `prodAux`, over any `CommRing`). -/
def cprodAux {R : Type*} [CommRing R] (H : Fin (L + 1) → ℕ)
    (A : ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) R) :
    (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) R
  | 0, _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) R)
  | k + 1, hk => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      refine (cprodAux H A k hk') * ?_
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨k, hkL⟩

/-- The full coefficient-polymorphic chain product `A⁽⁰⁾·…·A⁽ᴸ⁻¹⁾`. -/
def cprod {R : Type*} [CommRing R] (H : Fin (L + 1) → ℕ)
    (A : ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) R) :
    Matrix (Fin (H 0)) (Fin (H (Fin.last L))) R :=
  cprodAux H A L (Nat.lt_succ_self L)

/-- **`cprodAux` over `ℝ` is `prodAux`** (structural induction — `cprodAux` mirrors `prodAux`). -/
theorem cprodAux_eq_prodAux (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k < L + 1) :
    cprodAux H A k hk = prodAux H A k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [cprodAux, prodAux]
      congr 1
      exact ih (Nat.lt_of_succ_lt hk)

/-- **`cprod` over `ℝ` is `prod`**. -/
theorem cprod_eq_prod (H : Fin (L + 1) → ℕ) (A : Params H) : cprod H A = prod H A :=
  cprodAux_eq_prodAux H A L (Nat.lt_succ_self L)

/-- The `cprodAux` succ-step with the dependent-`Fin` cast hidden (cf. `LossHomogeneity.prodAux_step`):
if `A ⟨k,_⟩` is HEq to `Mstep`, then `cprodAux (k+1) = cprodAux k * Mstep`. -/
private theorem cprodAux_step {R : Type*} [CommRing R] (H : Fin (L + 1) → ℕ)
    (A : ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) R) (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) R)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    cprodAux H A (k + 1) hk = cprodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [cprodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)

/-- **`cprodAux` commutes with `Matrix.map` of a ring hom.** Induction on `k` via the cast-hidden
succ-step (the step matrix is HEq to the layer; `Matrix.map_mul` distributes over the product). -/
theorem cprodAux_map {R S : Type*} [CommRing R] [CommRing S] (H : Fin (L + 1) → ℕ) (f : R →+* S)
    (A : ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) R)
    (k : ℕ) (hk : k < L + 1) :
    (cprodAux H A k hk).map f = cprodAux H (fun s => (A s).map f) k hk := by
  induction k with
  | zero =>
      show (1 : Matrix (Fin (H 0)) (Fin (H 0)) R).map f = 1
      exact Matrix.map_one f (map_zero f) (map_one f)
  | succ k ih =>
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- the clean transported step matrix for `A` (HEq to `A ⟨k,hkL⟩`)
      let Mstep : Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) R := by
        rw [e1, e2]; exact A ⟨k, hkL⟩
      have hM : HEq (A ⟨k, hkL⟩) Mstep := by dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
      -- `Mstep.map f` is the step matrix for the `f`-mapped tuple (HEq to `(A ⟨k,hkL⟩).map f`)
      have hM' : HEq ((fun s => (A s).map f) ⟨k, hkL⟩) (Mstep.map f) := by
        show HEq ((A ⟨k, hkL⟩).map f) (Mstep.map f)
        cases e1; cases e2; cases (eq_of_heq hM); rfl
      rw [cprodAux_step H A k hk Mstep hM, Matrix.map_mul, ih hk',
        cprodAux_step H (fun s => (A s).map f) k hk (Mstep.map f) hM']

/-- **`cprod` commutes with `Matrix.map` of a ring hom.** -/
theorem cprod_map {R S : Type*} [CommRing R] [CommRing S] (H : Fin (L + 1) → ℕ) (f : R →+* S)
    (A : ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) R) :
    (cprod H A).map f = cprod H (fun s => (A s).map f) :=
  cprodAux_map H f A L (Nat.lt_succ_self L)

/-! ## The clean unit `U`, its polynomial encoding, and `eval u UPolyClean = U u` -/

variable (M : Fin (L + 1) → ℕ)

/-- The clean-chart unit factor `U(u) := dlnLoss M 0 (unblownParams u)` (the `u_p`-free factor of the
rate `routeMCore (cleanPhi u) = (u_p)²·U`, `= ‖prefix·M̄‖²`). -/
noncomputable def cleanUfun (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (u : Fin (routeMAmbient M) → ℝ) : ℝ :=
  dlnLoss M 0 (unblownParams M hL hne u)

/-- `cleanUfun ≥ 0` (a sum of squares). -/
theorem cleanUfun_nonneg (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (u : Fin (routeMAmbient M) → ℝ) : 0 ≤ cleanUfun M hL hne u :=
  dlnLoss_nonneg M 0 _

/-- The polynomial pivot-stripped flat vector: `c ↦ if c = p then C 1 else X c`. -/
noncomputable def unblownFlatPoly (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty) :
    Fin (routeMAmbient M) → MvPolynomial (Fin (routeMAmbient M)) ℝ :=
  fun c => if c = deepestPivot M hL hne then C 1 else X c

/-- `eval u ∘ unblownFlatPoly = unblownFlat u` (`eval u (C 1) = 1`, `eval u (X c) = u c`). -/
theorem eval_unblownFlatPoly (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (u : Fin (routeMAmbient M) → ℝ) (c : Fin (routeMAmbient M)) :
    MvPolynomial.eval u (unblownFlatPoly M hL hne c) = unblownFlat M hL hne u c := by
  rw [unblownFlatPoly, unblownFlat]
  by_cases hcp : c = deepestPivot M hL hne
  · rw [if_pos hcp, if_pos hcp, eval_C]
  · rw [if_neg hcp, if_neg hcp, eval_X]

/-- The polynomial parameter tuple: the `(s,i,j)` matrix slot is `unblownFlatPoly (flatCoordOf ⟨⟨s,i⟩,j⟩)`
(the polynomial mirror of `unblownParams`, via the decode `flatCoordOf`). -/
noncomputable def unblownParamsPoly (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty) :
    ∀ s : Fin L,
      Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) (MvPolynomial (Fin (routeMAmbient M)) ℝ) :=
  fun s => Matrix.of (fun i j => unblownFlatPoly M hL hne (flatCoordOf M ⟨⟨s, i⟩, j⟩))

/-- **`(unblownParamsPoly s).map (eval u) = unblownParams u s`** — the polynomial tuple maps under
`eval u` to the ℝ tuple (decode + `eval_unblownFlatPoly`). -/
theorem unblownParamsPoly_map_eval (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (u : Fin (routeMAmbient M) → ℝ) (s : Fin L) :
    (unblownParamsPoly M hL hne s).map (MvPolynomial.eval u) = unblownParams M hL hne u s := by
  funext i j
  rw [Matrix.map_apply, unblownParamsPoly, Matrix.of_apply, eval_unblownFlatPoly]
  exact (paramsEquivFlat_symm_decode M (unblownFlat M hL hne u) ⟨⟨s, i⟩, j⟩).symm

/-- **The polynomial clean unit `UPolyClean`** — the sum-of-squares of the polynomial chain product
`cprod` of `unblownParamsPoly`. -/
noncomputable def UPolyClean (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty) :
    MvPolynomial (Fin (routeMAmbient M)) ℝ :=
  ∑ i : Fin (M 0), ∑ j : Fin (M (Fin.last L)),
    (cprod M (unblownParamsPoly M hL hne) i j) ^ 2

/-- **`eval u UPolyClean = cleanUfun u`** — `eval u` pushes through `∑∑·²`; `cprod_map` + the
tuple-map identity give `eval u (cprod poly i j) = (prod M (unblownParams u)) i j`. -/
theorem eval_UPolyClean (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (u : Fin (routeMAmbient M) → ℝ) :
    MvPolynomial.eval u (UPolyClean M hL hne) = cleanUfun M hL hne u := by
  rw [UPolyClean, cleanUfun, dlnLoss]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_pow]
  -- `eval u (cprod poly i j) = (prod M (unblownParams u)) i j`
  have hcoe : MvPolynomial.eval u (cprod M (unblownParamsPoly M hL hne) i j)
      = (prod M (unblownParams M hL hne u)) i j := by
    have hmap : (cprod M (unblownParamsPoly M hL hne)).map (MvPolynomial.eval u)
        = cprod M (fun s => (unblownParamsPoly M hL hne s).map (MvPolynomial.eval u)) :=
      cprod_map M (MvPolynomial.eval u) (unblownParamsPoly M hL hne)
    have hfun : (fun s => (unblownParamsPoly M hL hne s).map (MvPolynomial.eval u))
        = unblownParams M hL hne u := by
      funext s; exact unblownParamsPoly_map_eval M hL hne u s
    rw [hfun] at hmap
    rw [cprod_eq_prod] at hmap
    have := congrFun (congrFun hmap i) j
    rw [Matrix.map_apply] at this
    exact this
  rw [hcoe]
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-! ## The all-ones witness: `UPolyClean ≠ 0`

At `u₁ ≡ 1` every entry of `unblownParams u₁` is `1` (the pivot if-branch is also `1`), so the tuple is
all-ones; the matrix-chain product of all-ones matrices is entrywise positive (each entry `= ∏ inner
widths > 0`, given all widths positive), so `U(u₁) ≥ (prod 0 0)² > 0`, hence `UPolyClean ≠ 0`. -/

/-- The all-ones layer tuple (every matrix entry `= 1`). -/
noncomputable def allOnesParams : Params M := fun _ => Matrix.of (fun _ _ => (1 : ℝ))

/-- The cast-clean succ-step matrix for `cprodAux` (HEq to `allOnesParams ⟨k,_⟩`). -/
private theorem cprodAux_allOnes_step (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (M ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (M ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (allOnesParams M ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    cprodAux M (allOnesParams M) (k + 1) hk
      = cprodAux M (allOnesParams M) k (Nat.lt_of_succ_lt hk) * Mstep :=
  cprodAux_step M (allOnesParams M) k hk Mstep hheq

/-- **The all-ones chain product is entrywise positive at `k+1`** (given all widths positive). The
prefix `cprodAux (k+1)` includes ≥ 1 all-ones factor; induction: base `cprodAux 1 = 1 * allOnes_0`
has each entry `= 1`; the step `(cprodAux (k+1)) * allOnes_{k+1}` is a sum over the nonempty
`Fin (M⟨k+1⟩)` of positive `(cprodAux (k+1))(i,l)·1`. -/
theorem cprodAux_allOnes_pos (hMpos : ∀ s, 0 < M s) (k : ℕ) (hk : k + 1 < L + 1)
    (i : Fin (M 0)) (j : Fin (M ⟨k + 1, hk⟩)) :
    0 < cprodAux M (allOnesParams M) (k + 1) hk i j := by
  induction k with
  | zero =>
      -- `cprodAux 1 = 1 * allOnes_0`; entry `= ∑_l 1[i=l]·1 = 1`
      have hkL : (0 : ℕ) < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨0, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1)) = (⟨0, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨0 + 1, hk⟩ : Fin (L + 1)) = (⟨0, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      let Mstep : Matrix (Fin (M ⟨0, Nat.lt_of_succ_lt hk⟩)) (Fin (M ⟨0 + 1, hk⟩)) ℝ := by
        rw [e1, e2]; exact allOnesParams M ⟨0, hkL⟩
      have hM : HEq (allOnesParams M ⟨0, hkL⟩) Mstep := by
        dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
      rw [cprodAux_allOnes_step M 0 hk Mstep hM, Matrix.mul_apply]
      -- `cprodAux 0 = 1`; `Mstep` is HEq all-ones so its entries are `1`
      have hMone : ∀ (a : Fin (M ⟨0, Nat.lt_of_succ_lt hk⟩)) (b : Fin (M ⟨0 + 1, hk⟩)),
          Mstep a b = 1 := by
        intro a b
        have : HEq Mstep (allOnesParams M ⟨0, hkL⟩) := hM.symm
        -- transfer the all-ones value across the HEq (cast the indices)
        cases e1; cases e2
        rw [eq_of_heq this]; rfl
      have hsum : (∑ x, (cprodAux M (allOnesParams M) 0 (Nat.lt_of_succ_lt hk)) i x * Mstep x j)
          = 1 := by
        refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) ?_).trans ?_
        · intro b _ hbi
          show (1 : Matrix (Fin (M 0)) (Fin (M 0)) ℝ) i b * Mstep b j = 0
          rw [Matrix.one_apply_ne (fun h => hbi h.symm), zero_mul]
        · show (1 : Matrix (Fin (M 0)) (Fin (M 0)) ℝ) i i * Mstep i j = 1
          rw [Matrix.one_apply_eq, hMone, mul_one]
      rw [hsum]; exact one_pos
  | succ k ih =>
      have hkL : k + 1 < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k + 1, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1)) = (⟨k + 1, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1 + 1, hk⟩ : Fin (L + 1)) = (⟨k + 1, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      let Mstep : Matrix (Fin (M ⟨k + 1, Nat.lt_of_succ_lt hk⟩)) (Fin (M ⟨k + 1 + 1, hk⟩)) ℝ := by
        rw [e1, e2]; exact allOnesParams M ⟨k + 1, hkL⟩
      have hM : HEq (allOnesParams M ⟨k + 1, hkL⟩) Mstep := by
        dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
      have hMone : ∀ (a : Fin (M ⟨k + 1, Nat.lt_of_succ_lt hk⟩)) (b : Fin (M ⟨k + 1 + 1, hk⟩)),
          Mstep a b = 1 := by
        intro a b; cases e1; cases e2; rw [eq_of_heq hM.symm]; rfl
      rw [cprodAux_allOnes_step M (k + 1) hk Mstep hM, Matrix.mul_apply]
      -- sum over the nonempty `Fin (M ⟨k+1,_⟩)` of `(cprodAux (k+1))(i,l)·1 > 0`
      have hnemp : Nonempty (Fin (M ⟨k + 1, Nat.lt_of_succ_lt hk⟩)) :=
        ⟨⟨0, hMpos _⟩⟩
      apply Finset.sum_pos
      · intro l _
        rw [hMone, mul_one]
        exact ih (Nat.lt_of_succ_lt hk) l
      · exact Finset.univ_nonempty

/-- **`U(allOnes) > 0`** — the loss at the all-ones tuple is a sum of squares containing the positive
`(prod 0 0)²` (`prod M (allOnes) = cprod M (allOnes)`, entrywise positive). Needs all widths positive
(`hMpos`) and the index `(0,0)` (`M 0, M (last) ≥ 1`). -/
theorem dlnLoss_allOnes_pos {L : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ s, 0 < M s) :
    0 < dlnLoss M 0 (allOnesParams M) := by
  -- write `L = n+1` so the product unfolds to a succ-step
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  -- `prod M (allOnes) (0,0) > 0` via `cprodAux_allOnes_pos` at `k+1 = L = n+1`
  have hpos00 : 0 < prod M (allOnesParams M) ⟨0, hMpos 0⟩ ⟨0, hMpos (Fin.last (n + 1))⟩ := by
    rw [← cprod_eq_prod, cprod]
    exact cprodAux_allOnes_pos M hMpos n (Nat.lt_succ_self (n + 1)) ⟨0, hMpos 0⟩
      ⟨0, hMpos (Fin.last (n + 1))⟩
  -- `dlnLoss = ∑∑ (prod - 0)² ≥ (prod 0 0)² > 0`
  rw [dlnLoss]
  apply Finset.sum_pos'
  · exact fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)
  · refine ⟨⟨0, hMpos 0⟩, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · exact fun j _ => sq_nonneg _
    · refine ⟨⟨0, hMpos (Fin.last (n + 1))⟩, Finset.mem_univ _, ?_⟩
      simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
      exact pow_pos hpos00 2

/-- **`UPolyClean ≠ 0`** — it evaluates to `U(allOnes) > 0` at the all-ones point `u₁ ≡ 1`. -/
theorem UPolyClean_ne_zero (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (hMpos : ∀ s, 0 < M s) :
    UPolyClean M hL hne ≠ 0 := by
  intro h0
  have hval : MvPolynomial.eval (fun _ => (1 : ℝ)) (UPolyClean M hL hne)
      = cleanUfun M hL hne (fun _ => 1) := eval_UPolyClean M hL hne _
  rw [h0, map_zero] at hval
  -- `cleanUfun u₁ = dlnLoss M 0 (unblownParams u₁) = dlnLoss M 0 (allOnes) > 0`
  have honeAll : unblownParams M hL hne (fun _ => 1) = allOnesParams M := by
    funext s i j
    -- decode + `unblownFlat (fun _ => 1) c = 1` (both if-branches give `1`)
    rw [unblownParams,
      paramsEquivFlat_symm_decode M (unblownFlat M hL hne (fun _ => 1)) ⟨⟨s, i⟩, j⟩, unblownFlat]
    show (if flatCoordOf M ⟨⟨s, i⟩, j⟩ = deepestPivot M hL hne then (1 : ℝ) else 1)
      = allOnesParams M s i j
    rw [ite_self]; rfl
  rw [cleanUfun, honeAll] at hval
  exact absurd hval (ne_of_gt (dlnLoss_allOnes_pos M hL hMpos)).symm

/-! ## The assembled `Ubound` / `Umeas` fields for the clean chart -/

/-- **`cleanUfun` is continuous** — it equals `eval u UPolyClean`, a polynomial map. -/
theorem continuous_cleanUfun (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty) :
    Continuous (cleanUfun M hL hne) := by
  have heq : cleanUfun M hL hne
      = fun u => MvPolynomial.eval u (UPolyClean M hL hne) := by
    funext u; exact (eval_UPolyClean M hL hne u).symm
  rw [heq]; exact MvPolynomial.continuous_eval _

/-- **`cleanUfun` is measurable.** -/
theorem measurable_cleanUfun (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty) :
    Measurable (cleanUfun M hL hne) :=
  (continuous_cleanUfun M hL hne).measurable

/-- **`cleanUfun > 0` a.e.** — `U = eval UPolyClean`, `UPolyClean ≠ 0` (the all-ones witness), so the
zero set is Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`); off it `U ≥ 0` is `> 0`. -/
theorem cleanUfun_ae_pos (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (hMpos : ∀ s, 0 < M s) :
    ∀ᵐ u : Fin (routeMAmbient M) → ℝ, 0 < cleanUfun M hL hne u := by
  have hae := MvPolynomial.ae_eval_ne_zero _ (UPolyClean_ne_zero M hL hne hMpos)
  filter_upwards [hae] with u hu
  rw [eval_UPolyClean M hL hne u] at hu
  exact lt_of_le_of_ne (cleanUfun_nonneg M hL hne u) (Ne.symm hu)

/-- **`cleanUfun ≤ B` on the box `[0,δ]^N`** (continuous on a compact box). -/
theorem cleanUfun_le_on_box (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty) (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
      cleanUfun M hL hne u ≤ B := by
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty
    with he | hne'
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne' (continuous_cleanUfun M hL hne).continuousOn
    exact ⟨max 1 (cleanUfun M hL hne u0), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-- **The full clean `Ubound` field** (box-bound + a.e.-positivity), under all-widths-positive `hMpos`. -/
theorem cleanUbound (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty) (hMpos : ∀ s, 0 < M s) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        cleanUfun M hL hne u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < cleanUfun M hL hne u := by
  intro δ
  obtain ⟨B, hB0, hBle⟩ := cleanUfun_le_on_box M hL hne δ
  exact ⟨B, hB0, hBle, ae_restrict_of_ae (cleanUfun_ae_pos M hL hne hMpos)⟩

end DLNFibre.DLN.RLCT
