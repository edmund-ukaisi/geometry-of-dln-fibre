import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotFin

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitFin` — Brick D join, full-matBox route (`genm-sj5-finfin`)

**Thread `genm-sj5-finfin` (aoyagi-full Stage 2).** The full-matBox head-split domination that makes
`headSplit_domination_impl` sorry-free for ALL `j` (the `j ≥ 1` cover shells). Sits downstream of
`RouteMSJPivotFin` so it can reuse the shell-INDEPENDENT ratio-trick plumbing (`pivotDomRHS_ne_zero_aux`,
`pivotDomRHS_eq_top_of_critical`, `exists_finite_mul_of_finite_imp`) and the block-front reassembly
(`pivotInner_Dsubst`, `blockFront_inner_eq`). It supersedes the placeholder `headSplit_pivotDom` /
`shellSpine_le_hsQ_box` / `headSplit_domination_impl` that `genm-sj5-pradial` left as sorries in
`RouteMSJHeadSplitDom`; those are relocated here (the from-scratch analytic module the docstring flagged).

## What lands (sorry-free)

* **`spine_submatrix_eq_hsQ`** — on the shell (where `Zf z = deeperFlagZdeep`), the spine's row-reindexed
  front factor `(prod (tailChain M) A').submatrix (blockSplitEquiv κ) id` IS `hsQ`. The pivot (`inl`)
  block is `rfl` (all `finCongr`/`blockSplitEquiv` reductions are definitional); the corank (`inr`) block
  uses `hZfeq`. The mathematical heart of the reorganization.
* **`hsSplit_preimage_box`** — the box factorization `hsSplit ⁻¹' (paramsBox × matBox) = paramsBox`
  (via the forward-action lemmas + `blockSplitEquiv` row-surjectivity).
* **`Hfull_eq_Hblock`** — the freed-`Γ` spine inner integral equals the block-front integral over the
  fixed block box (`pivotInner_Dsubst` per `x` on `outerDom` + `blockFront_inner_eq`); this converts the
  `x`-dependent `Γ`-domain to a FIXED block domain, making the inner integral parametrically measurable.
* **`shellSpine_le_hsQ_box`** — the pure measure reorganization onto the FULL `matBox` (brick B): enlarge
  the shell domain to the good preimage `paramsBox ∩ E` (`E` measurable via `hGmeas` — this is why the
  good set, not the shell, is the intermediate; the shell's own measurability is never needed), rewrite
  the spine integrand to `Hfull ∘ hsSplit` there, enlarge to the full box, transport (MP `hsSplit`),
  Tonelli-uncurry.
* **`headSplit_pivotDom`** — brick A, the FULL-matBox domination, via the ratio trick
  (`exists_finite_mul_of_finite_imp` + `pivotDomRHS_ne_zero_aux`; the comparator threshold extracted by
  `pivotDomRHS_eq_top_of_critical`). The genuine content is isolated as `pivotDomLHS_full_lt_top`.
* **`headSplit_domination_impl`** — the join `shellSpine_le_hsQ_box ∘ headSplit_pivotDom`; verbatim the
  `RouteMSJDeeperFlagCore.headSplit_domination` stub conclusion. The controller wires the stub to it.

## The one isolated analytic wall (SD-7)

* **`pivotDomLHS_full_lt_top`** — `2c' < minAdm(redChain u M) + (M₀−u)(M₁−u)` (⇔ `c' < carrierThreshold`)
  and the deep-factor floor `hfloor` ⟹ the full-matBox spine LHS is finite. This is the marginal
  (`λ_full = carrierThreshold`, reconciled SOUND by `genm-sj5-pradial`'s decorrelated Codex + Monte-Carlo)
  rank-drop finiteness. Its route (couplingfin-adjudicated bounded, NOT shell-0): unit-Jacobian column-shear
  `Q_p R = [I|0]`, `Q_b R = (…,s)` giving the local normal form `L ≍ |x|² + s²|y|²`; the banked coupled
  corank peel `shell_corankPivot_coupled_le` for the `ab/2` charge + det-Gram divisor (integrable via
  `hfloor` — `uniformWenn_proj_le` + `strongBlock_lintegral_lt_top`, `a < m−b+1` from `hcvg`); the transverse
  `s`-charge `= ½` matching. The column-shear normal-form change-of-variables is genuine new machinery (NOT
  banked) — a from-scratch analytic module for a next tide. Kept over the FULL matBox ∀j; the bound comes
  from the DEEP-factor floor on `Z_deep` (never `σ_min(hsQ) ≥ ε`, which is false for `j ≥ 1`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **On the shell, the spine's row-reindexed front factor equals `hsQ`.** Given `Zf z = deeperFlagZdeep`
(the good-set agreement, `z = (hsSplit A').1`), the shell spine's `Q = (prod (tailChain M) A').submatrix
(blockSplitEquiv κ) id` equals `hsQ M u Zf z A_cor` (`A_cor = (hsSplit A').2`). Pivot (`inl`) block: `rfl`
(the `finCongr` row/col casts and `blockSplitEquiv_inl` are definitional through `prod_headSplit`); corank
(`inr`) block: `hZfeq` on `A_cor·Zf z = A_cor·Z_deep`. -/
theorem spine_submatrix_eq_hsQ (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (A' : Params (tailChain M))
    (hZfeq : Zf ((hsSplit M (t + j) κ A').1)
      = deeperFlagZdeep M (t + j) ((hsSplit M (t + j) κ A').1)) :
    (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id
      = hsQ M (t + j) Zf ((hsSplit M (t + j) κ A').1) ((hsSplit M (t + j) κ A').2) := by
  have hZd : deeperFlagZdeep M (t + j) ((hsSplit M (t + j) κ A').1)
      = prod (dropHead (tailChain M)) (fun s => A' s.succ) := rfl
  rw [hsQ, prod_headSplit (tailChain M) A',
    prod_headSplit (redChain (t + j) M) ((hsSplit M (t + j) κ A').1)]
  ext I k
  cases I with
  | inl i => rfl
  | inr i =>
      simp only [Matrix.submatrix_apply, Matrix.fromRows_apply_inr, id_eq, Matrix.mul_apply,
        Matrix.of_apply, rmatMul]
      rw [hZfeq]
      rfl

/-- **The freed-`Γ` spine inner integral equals the block-front inner integral.** Per `x ∈ outerDom`
(so `IsUnit P`), `pivotInner_Dsubst` turns the shifted-`Γ` integral into the raw `D ∈ genBox` integral;
`blockFront_inner_eq` reassembles `(x, D)` over `outerDom × genBox` into the single block-box integral.
Converts the `x`-dependent `Γ`-domain to the FIXED block domain (needed for parametric measurability). -/
theorem Hfull_eq_Hblock (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (c' : ℝ) (z : Params (redChain u M))
    (A_cor : Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) :
    (∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c')))
      = ∫⁻ B in genBox (Fin u ⊕ Fin (M 0 - u)) (Fin u ⊕ Fin (M 1 - u)) 1
          ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal (frobSq (Matrix.of B * hsQ M u Zf z A_cor) ^ (-c')) := by
  rw [show (∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c')))
      = ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
          ∫⁻ D in genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1,
            ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD u (M 0 - u) (M 1 - u)).symm (x, D))
              * hsQ M u Zf z A_cor) ^ (-c')) from
      setLIntegral_congr_fun (measurableSet_outerDom u (M 0 - u) (M 1 - u) 1)
        (fun x hx => pivotInner_Dsubst x hx.2.2.2 (hsQ M u Zf z A_cor) c')]
  exact blockFront_inner_eq (hsQ M u Zf z A_cor) c'

/-- **The `hsSplit` box factorization** `hsSplit ⁻¹' (paramsBox × matBox) = paramsBox`. `hsSplit` shuffles
the leading tail layer's rows (pivot via `κ`, corank) and re-glues onto the deep layers — a coordinate
rearrangement preserving the `[−1,1]` box; proved via the forward-action lemmas + `blockSplitEquiv`
row-surjectivity. -/
theorem hsSplit_preimage_box (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1)) :
    hsSplit M u κ ⁻¹' (paramsBoxM (redChain u M) 1
        ×ˢ matBox (M 1 - u) (dropHead (redChain u M) 0) 1)
      = paramsBoxM (tailChain M) 1 := by
  ext A'
  simp only [Set.mem_preimage, paramsBoxM, matBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hcork⟩ s
    refine Fin.cases ?_ (fun s' => ?_) s
    · intro i k
      obtain ⟨S, hS⟩ := (blockSplitEquiv κ).surjective i
      cases S with
      | inl a =>
          have hzik := hz 0 a k
          rw [hsSplit_fst_zero] at hzik
          rw [← hS]; exact hzik
      | inr b =>
          have hck := hcork b k
          rw [hsSplit_snd] at hck
          rw [← hS]; exact hck
    · intro i k
      have hzik := hz s'.succ i k
      rw [hsSplit_fst_succ] at hzik
      exact hzik
  · intro h
    refine ⟨fun s => ?_, fun b k => ?_⟩
    · refine Fin.cases ?_ (fun s' => ?_) s
      · intro a k; rw [hsSplit_fst_zero]; exact h 0 _ k
      · intro i k; rw [hsSplit_fst_succ]; exact h s'.succ i k
    · rw [hsSplit_snd]; exact h 0 _ k

/-- **`hsQ` entries are measurable in the `(z, A_cor)` pair** (given `Zf` measurable). The pivot (`inl`)
entry reads a `prod (redChain u M) z` matrix element (`continuous_prod`); the corank (`inr`) entry is
`(A_cor · Zf z)` (a finite sum of products of measurable projections). Entry-level to avoid the missing
`MeasurableSpace (Matrix …)` instance. -/
theorem measurable_hsQ_entry (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (J : Fin u ⊕ Fin (M 1 - u)) (k : Fin (dropHead (redChain u M) (Fin.last L))) :
    Measurable (fun p : Params (redChain u M)
        × (Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) =>
      hsQ M u Zf p.1 p.2 J k) := by
  cases J with
  | inl i =>
      simp only [hsQ, Matrix.fromRows_apply_inl, Matrix.submatrix_apply, finCongr_apply]
      exact ((continuous_prod (redChain u M)).matrix_elem _ _).measurable.comp measurable_fst
  | inr i =>
      simp only [hsQ, Matrix.fromRows_apply_inr, Matrix.mul_apply, Matrix.of_apply]
      refine Finset.measurable_sum _ (fun n _ => ?_)
      exact ((measurable_pi_apply n).comp ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply k).comp ((measurable_pi_apply n).comp (hZfMeas.comp measurable_fst)))

/-- **The block-front scalar integrand is jointly measurable in `((z, A_cor), B)`.** Entrywise expansion
of `frobSq (of B · hsQ)` (products/sums of `B`-projections and `hsQ` entries, `measurable_hsQ_entry`),
wrapped in `rpow`/`ofReal`. -/
theorem measurable_blockFront_integrand (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf) (c' : ℝ) :
    Measurable (fun q :
        (Params (redChain u M) × (Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ))
        × ((Fin u ⊕ Fin (M 0 - u)) → (Fin u ⊕ Fin (M 1 - u)) → ℝ) =>
      ENNReal.ofReal (frobSq (Matrix.of q.2 * hsQ M u Zf q.1.1 q.1.2) ^ (-c'))) := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq
  refine Finset.measurable_sum _ (fun I _ => Finset.measurable_sum _ (fun k _ => ?_))
  refine Measurable.pow_const ?_ 2
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ (fun J _ => Measurable.mul ?_ ?_)
  · exact (measurable_pi_apply J).comp ((measurable_pi_apply I).comp measurable_snd)
  · exact (measurable_hsQ_entry M u Zf hZfMeas J k).comp measurable_fst

/-- **The block-front inner integral is measurable in `(z, A_cor)`** (`Measurable.lintegral_prod_right`
over the FIXED block box). -/
theorem measurable_Hblock (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf) (c' : ℝ) :
    Measurable (fun p : Params (redChain u M)
        × (Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) =>
      ∫⁻ B in genBox (Fin u ⊕ Fin (M 0 - u)) (Fin u ⊕ Fin (M 1 - u)) 1
          ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
        ENNReal.ofReal (frobSq (Matrix.of B * hsQ M u Zf p.1 p.2) ^ (-c'))) :=
  (measurable_blockFront_integrand M u Zf hZfMeas c').lintegral_prod_right

/-- **Freed-loss rewrite across the column-type gap.** `freedSchurLoss x Γ (spine Q) = freedSchurLoss x
Γ (hsQ …)` via `spine_submatrix_eq_hsQ` (the two column types `tailChain M (last)` and `dropHead
(redChain u M) (last)` are defeq, so `rw` + `rfl` bridges them). -/
theorem spine_freedLoss_eq (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (A' : Params (tailChain M))
    (hZfeq : Zf ((hsSplit M (t + j) κ A').1)
      = deeperFlagZdeep M (t + j) ((hsSplit M (t + j) κ A').1))
    (x : SJOuter (t + j) (M 0 - (t + j)) (M 1 - (t + j)))
    (Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ) :
    freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)
      = freedSchurLoss x Γ
          (hsQ M (t + j) Zf ((hsSplit M (t + j) κ A').1) ((hsSplit M (t + j) κ A').2)) := by
  rw [spine_submatrix_eq_hsQ M t j κ Zf A' hZfeq]
  rfl

/-- **Measurability of the `z`-projection of `hsSplit`.** -/
theorem measurable_hsSplit_fst (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1)) :
    Measurable (fun A' : Params (tailChain M) => (hsSplit M u κ A').1) :=
  measurable_fst.comp (hsSplit M u κ).measurable

/-- **Brick B — the head/row-split bridge onto the FULL matBox** (pure measure reorganization). The
literal shell-`j` spine integrand is `≤` the `(z, A_cor)`-box freed-loss integrand at `Q = hsQ`, with
`A_cor` over the FULL `matBox` (NO `pivotShell`). Route: enlarge the shell domain to the GOOD preimage
`paramsBox ∩ E` (`E := (hsSplit ·).1 ⁻¹' goodSet`, measurable via `hGmeas` — the shell's own measurability
is never invoked; `hsSplit_good_of_shell` gives `shell ⊆ E`), rewrite the spine integrand to `Hfull ∘
hsSplit` there (`spine_freedLoss_eq`), enlarge to the full box (`≥ 0`), transport (MP `hsSplit` +
`hsSplit_preimage_box`), Tonelli-uncurry (`Hfull` measurable via `Hfull_eq_Hblock` + `measurable_Hblock`).
NO analytic content. -/
theorem shellSpine_le_hsQ_box {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε') (hε'le : ε' ≤ ε / Real.sqrt ((M 1 : ℝ) * M 2))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z)
    (hGmeas : MeasurableSet {z : Params (redChain (t + j) M) |
        weakEigCount ε' (deeperFlagZdeep M (t + j) z)
          ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)}) :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ ∫⁻ z in paramsBoxM (redChain (t + j) M) 1,
          ∫⁻ A_cor in matBox (M 1 - (t + j)) (dropHead (redChain (t + j) M) 0) 1,
            ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
              ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
                  Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
                ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf z A_cor)) ^ (-c')) := by
  classical
  -- the freed-Γ spine inner integral as a function of the reduced pair `(z, A_cor)`
  set Hfull : Params (redChain (t + j) M)
      × (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ) → ℝ≥0∞ :=
    fun p => ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf p.1 p.2)) ^ (-c')) with hHfulldef
  have hHfullMeas : Measurable Hfull := by
    have hEq : Hfull = fun p => ∫⁻ B in genBox (Fin (t + j) ⊕ Fin (M 0 - (t + j)))
          (Fin (t + j) ⊕ Fin (M 1 - (t + j))) 1 ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal (frobSq (Matrix.of B * hsQ M (t + j) Zf p.1 p.2) ^ (-c')) := by
      funext p; rw [hHfulldef]; exact Hfull_eq_Hblock M (t + j) Zf c' p.1 p.2
    rw [hEq]; exact measurable_Hblock M (t + j) Zf hZfMeas c'
  set E : Set (Params (tailChain M)) :=
    (fun A' => (hsSplit M (t + j) κ A').1) ⁻¹' {z | weakEigCount ε' (deeperFlagZdeep M (t + j) z)
      ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)} with hEdef
  have hEmeas : MeasurableSet (paramsBoxM (tailChain M) 1 ∩ E) :=
    (paramsBoxM_measurableSet (tailChain M)).inter ((measurable_hsSplit_fst M (t + j) κ) hGmeas)
  rw [shellSpineIntegrand]
  have hsub : (paramsBoxM (tailChain M) 1
        ∩ {A' | prod (tailChain M) A' ∈ singularShell ε (min (M 0 - t) (M 1 - t))
            ⟨j, Nat.lt_succ_of_le hj⟩})
      ⊆ paramsBoxM (tailChain M) 1 ∩ E := fun A' hA' =>
    Set.mem_inter hA'.1 (hsSplit_good_of_shell M t j κ hε hj hjr hε' hε'le A' hA'.1 hA'.2)
  refine le_trans (lintegral_mono_set hsub) ?_
  have hcongr : ∀ A' ∈ paramsBoxM (tailChain M) 1 ∩ E,
      (∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')))
        = Hfull (hsSplit M (t + j) κ A') := by
    intro A' hA'
    have hZfeq : Zf ((hsSplit M (t + j) κ A').1)
        = deeperFlagZdeep M (t + j) ((hsSplit M (t + j) κ A').1) :=
      hagree ((hsSplit M (t + j) κ A').1) hA'.2
    rw [hHfulldef]
    exact lintegral_congr (fun x => lintegral_congr (fun Γ => by
      rw [spine_freedLoss_eq M t j κ Zf A' hZfeq x Γ]))
  rw [setLIntegral_congr_fun hEmeas hcongr]
  refine le_trans (lintegral_mono_set Set.inter_subset_left) ?_
  rw [← hsSplit_preimage_box M (t + j) κ,
    (measurePreserving_hsSplit M (t + j) κ).setLIntegral_comp_preimage_emb
      (hsSplit M (t + j) κ).measurableEmbedding Hfull
      (paramsBoxM (redChain (t + j) M) 1
        ×ˢ matBox (M 1 - (t + j)) (dropHead (redChain (t + j) M) 0) 1)]
  exact le_of_eq (setLIntegral_prod
    (μ := (volume : Measure (Params (redChain (t + j) M))))
    (ν := (volume : Measure (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ)))
    Hfull hHfullMeas.aemeasurable)

/-- **The full-matBox spine LHS** — the freed Schur-loss spine integrand at `Q = hsQ`, integrated over
`(z, A_cor, x, Γ)` with `A_cor` over the FULL `matBox` (NO `pivotShell`). -/
noncomputable def pivotDomLHS_full (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) : ℝ≥0∞ :=
  ∫⁻ z in paramsBoxM (redChain u M) 1,
    ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1,
      ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c'))

/-- **The full-matBox tight finiteness (the ISOLATED analytic wall, SD-7).** Below the comparator
threshold `2c' < minAdm(redChain u M) + (M₀−u)(M₁−u)` (⇔ `c' < carrierThreshold`), and given the
deep-factor floor `hfloor` (`Zf·Zfᵀ ⪰ ε'²·U_sf·U_sfᵀ`, `U_sf` orthonormal `m`-frame, `m ≥ a+b`), the
full-matBox spine LHS is finite.

RECONCILED SOUND (`genm-sj5-pradial`, decorrelated Codex xhigh + Monte-Carlo): the full-matBox route is
marginal, `λ_full = (minAdm+ab)/2 = carrierThreshold` EXACTLY (the rank-drop codim-1 locus lowers the shell
threshold `(u+a)(u+b)/2` to `carrierThreshold`, matching the comparator). ROUTE (couplingfin-adjudicated
bounded, NOT shell-0): local normal form `L ≍ |x|² + s²|y|²` via the unit-Jacobian column-shear `Q_p R =
[I|0]`, `Q_b R = (…,s)` (`s = σ_min(hsQ)`, the transverse `A`-coordinate) — the inner `T`-integral scales
`g^{−(c'−ab/2)}` (`g = σ_min²`), the outer transverse integral `∫ |s|^{−2(c'−ab/2)}` converges iff `c' <
carrierThreshold`; the `ab/2` charge + det-Gram divisor from the banked coupled corank peel
`shell_corankPivot_coupled_le` (integrable via `hfloor`: `uniformWenn_proj_le` + `strongBlock_lintegral_lt_top`,
`a < m−b+1` from `hcvg`); the transverse `s`-charge `= ½` matching. The column-shear normal-form
change-of-variables is genuine NEW machinery (not banked) — a from-scratch analytic module for a next tide.

ANTI-REGRESSION (bedrock): the bound MUST come from the DEEP-factor floor `hfloor` on `Z_deep`, over the
FULL matBox ∀j; it must NEVER route through `σ_min(hsQ) ≥ ε` (false for `j ≥ 1` — the shell-0 route
`RouteMSJPivotFin.pivotDomLHS_lt_top_of_pos` does NOT transfer) nor silently drop the `ab/2` charge. -/
theorem pivotDomLHS_full_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : 1 ≤ u)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hc0 : 0 ≤ c') (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) {m : ℕ}
    (hcvg : (M 0 - u) + (M 1 - u) ≤ m) (hmM : m ≤ dropHead (redChain u M) 0)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (U_sf : Params (redChain u M) → Matrix (Fin (dropHead (redChain u M) 0)) (Fin m) ℝ)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, m ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hcrit : 2 * c' < ((minAdm (redChain u M) + (M 0 - u) * (M 1 - u) : ℕ) : ℝ)) :
    pivotDomLHS_full M u c' Zf < ⊤ := by
  sorry

/-- **Brick A — the FULL-matBox head-split domination (GLUE-2).** On the `(z, A_cor)`-box with `A_cor`
over the FULL `matBox`, the freed Schur-loss spine integrand is dominated by a FINITE constant times the
comparator-core integrand at the clean data `k = ![1]`, `jc = ![minAdm − 1]`, `Ccrossf = 0`, `sΓf =
genBox`. Ratio trick (`RHS = ⊤ → C := 1`; `RHS < ⊤ → C := LHS/RHS`, finite by `pivotDomLHS_full_lt_top`,
nonzero denominator by `pivotDomRHS_ne_zero_aux`); the threshold `2c' < minAdm + ab` is extracted from
`RHS < ⊤` via `pivotDomRHS_eq_top_of_critical`. `hu : 1 ≤ u` (supplied from `ht1 : 1 ≤ t` at the call). -/
theorem headSplit_pivotDom (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : 1 ≤ u)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hc0 : 0 ≤ c') (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) {m : ℕ}
    (hcvg : (M 0 - u) + (M 1 - u) ≤ m) (hmM : m ≤ dropHead (redChain u M) 0)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (U_sf : Params (redChain u M) → Matrix (Fin (dropHead (redChain u M) 0)) (Fin m) ℝ)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, m ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef) :
    ∃ (C_hle : ℝ≥0∞), C_hle < ⊤
      ∧ (∫⁻ z in paramsBoxM (redChain u M) 1,
            ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1,
              ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
                ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
                    Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
                  ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c')))
          ≤ C_hle * deeperFlagCoreIntegrand M u (![1] : Fin 1 → ℕ)
              (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) Zf
              (fun _ => 0) (fun _ => genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1) c' := by
  change ∃ C_hle : ℝ≥0∞, C_hle < ⊤ ∧ pivotDomLHS_full M u c' Zf ≤ C_hle * pivotDomRHS M u c' Zf
  refine exists_finite_mul_of_finite_imp
    (pivotDomRHS_ne_zero_aux M u hu c' hc0 hnd Zf hZfMeas) (fun hRHS => ?_)
  have hcrit : 2 * c' < ((minAdm (redChain u M) + (M 0 - u) * (M 1 - u) : ℕ) : ℝ) := by
    by_contra hcon
    rw [pivotDomRHS_eq_top_of_critical M u hu c' hnd Zf hZfMeas
      (by rw [not_lt] at hcon; push_cast at hcon ⊢; linarith)] at hRHS
    exact lt_irrefl _ hRHS
  exact pivotDomLHS_full_lt_top M u hu hε c' hc0 hnd hpiv hcvg hmM hε' Zf U_sf hUs hrank hfloor hcrit

/-- **Brick D (isolated): the head-split domination with a FINITE reorganization constant.** Verbatim
conclusion of the `RouteMSJDeeperFlagCore.headSplit_domination` stub (with the shell-threaded extra
hypotheses `hc0`/`hjr`/`hε'le`/`hGmeas` the wiring supplies); the controller wires the stub to it. Composes
brick B (`shellSpine_le_hsQ_box`) and brick A (`headSplit_pivotDom`) by `le_trans`, with witnesses
`Ccrossf = 0`, `sΓf = genBox`. -/
theorem headSplit_domination_impl {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hc0 : 0 ≤ c')
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε') (hε'le : ε' ≤ ε / Real.sqrt ((M 1 : ℝ) * M 2))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (U_sf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (min (M 1) (M (Fin.last (L + 1 + 1))) - j)) ℝ)
    (hZfMeas : Measurable Zf) (hUsMeas : Measurable U_sf)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, (min (M 1) (M (Fin.last (L + 1 + 1))) - j) ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z)
    (hGmeas : MeasurableSet {z : Params (redChain (t + j) M) |
        weakEigCount ε' (deeperFlagZdeep M (t + j) z)
          ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)}) :
    ∃ (Ccrossf : Params (redChain (t + j) M)
          → Matrix (Fin (M 0 - (t + j))) (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
        (sΓf : Params (redChain (t + j) M)
          → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
        (C_hle : ℝ≥0∞),
      C_hle < ⊤
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) (![1] : Fin 1 → ℕ)
              (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) Zf Ccrossf sΓf c' := by
  refine ⟨fun _ => 0, fun _ => genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1, ?_⟩
  have hmM : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ dropHead (redChain (t + j) M) 0 := by
    rw [dropHead_redChain_zero]; exact hrange
  obtain ⟨C_hle, hfin, hle⟩ :=
    headSplit_pivotDom M (t + j) (by omega) hε c' hc0 hnd hpiv
      (m := min (M 1) (M (Fin.last (L + 1 + 1))) - j) hcvg hmM hε' Zf hZfMeas U_sf hUs hrank hfloor
  refine ⟨C_hle, hfin, ?_⟩
  exact le_trans
    (shellSpine_le_hsQ_box M t j κ hε c' ht hj hjr ht1 hnd hrange hε' hε'le Zf hZfMeas hagree hGmeas)
    hle

end DLNFibre.DLN.RLCT
