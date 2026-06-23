import DLNFibre.DLN.RLCT.Foundations.Loss
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestTelescoping` — the PIN2 endpoint-frame telescoping

The cast-heavy `prodAux` induction behind PIN2's frame bridge:
`∏C = P₀ · (∏A) · Q_{L-1}` when each layer is framed `C s = P s · A s · Q s` and the interior
interfaces cancel (`Q s · P (s+1) = 1`). Stated with EXISTENTIAL endpoints (cobuild's banked
statement-shape, `@eee22a1`) to dodge the `H 0` vs `H ⟨0,_⟩.castSucc` definitional mismatch.

**STATUS (crux2 2026-06-23): the cast mechanics are DE-RISKED, the induction is the XL-cast — DEFERRED
to a fresh-session-with-Codex (HEq-induction design), per controller's 3-attempt discipline.** Two
findings shape the eventual proof:
- (PROBE 1, BUILDS) the running-width identifications `H ⟨k,hk⟩` and `H (⟨k,hkL⟩.castSucc)` are
  DEFINITIONALLY `rfl` (Fin proof-irrelevance + `castSucc ⟨k,_⟩` reduction). So the index VALUES agree
  freely — the obstacle is purely the elaborator's `HMul` instance synthesis, NOT a real value-mismatch.
- (`prodAux_succ` SHAPE, typechecks) the `k+1` fold IS the running product times the layer transported
  by `Matrix.reindex (finCongr ·) (finCongr ·)` (the explicit form of the def's `rw [e1,e2]`). This is
  the right unfold; its `rfl`-discharge needs an entry-chase through `reindex_apply` vs the def's `Eq.mpr`
  cast — the bridge that wants Codex's design (3-attempt cap hit on the entry-chase).
The `endpoint_telescoping` statement-SHAPE is cobuild's (`@eee22a1`); it typechecks (signature GREEN).
The remaining work is the prefix-fold induction with interface-cancellation in the reindexed types.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **DE-RISK PROBE 1 (BUILDS `rfl`).** The two running-width identifications are definitionally equal —
the index values agree freely; only `HMul` instance synthesis (not a value-mismatch) is the obstacle. -/
example (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k + 1 < L + 1) :
    H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
      = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) := rfl

/-- **`prodAux` recursion, reindex-explicit** (statement TYPECHECKS; proof is the deferred entry-chase).
The `k+1` fold is the running product times the `k`-th layer, transported to the running-width type by
`Matrix.reindex (finCongr ·) (finCongr ·)` — the explicit form of the def's `rw [e1,e2]; exact A …`. -/
theorem prodAux_succ (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (e1 : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
    (e2 : H (⟨k + 1, hk⟩ : Fin (L+1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) :
    prodAux H A (k + 1) hk
      = (prodAux H A k (Nat.lt_of_succ_lt hk)) *
          (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩)) := by
  obtain rfl : e1 = rfl := Subsingleton.elim _ _
  obtain rfl : e2 = rfl := Subsingleton.elim _ _
  rfl

/-- **SHARED step-cast helper** (#123, the family kernel). If the `k`-th layer of `A` is the reindexed
block `Matrix.reindex eC.symm eS.symm M` at the running widths, then the `prodAux` succ-step is the clean
product `prodAux k * reindex eC.symm eS.symm M` — the def's `Eq.mpr` cast is collapsed by the index-level
`cases e1; cases e2` idiom (the `contDiff_prodAux_entry` precedent). All three folds (value / deriv /
telescope) apply this then their own block-composition. `eC, eS` are the threshold splits at `H ⟨k,hk'⟩`,
`H ⟨k+1,hk⟩`. -/
theorem prodAux_succ_layer (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    {p q : ℕ} (eC : Fin (H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1))) ≃ Fin p ⊕ Fin q)
    {p' q' : ℕ} (eS : Fin (H (⟨k + 1, hk⟩ : Fin (L+1))) ≃ Fin p' ⊕ Fin q')
    (M : Matrix (Fin p ⊕ Fin q) (Fin p' ⊕ Fin q') ℝ)
    (hlayer : A (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L)
      = (by rw [show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc
                = (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1)) from by apply Fin.ext; simp [Fin.castSucc],
              show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ
                = (⟨k + 1, hk⟩ : Fin (L+1)) from by apply Fin.ext; simp [Fin.succ]]
            exact Matrix.reindex eC.symm eS.symm M :
          Matrix (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
            (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) ℝ)) :
    prodAux H A (k + 1) hk
      = prodAux H A k (Nat.lt_of_succ_lt hk) * Matrix.reindex eC.symm eS.symm M := by
  have hkL : k < L := Nat.lt_of_succ_lt_succ hk
  have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
  have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
    apply Fin.ext; simp [Fin.castSucc]
  have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
    apply Fin.ext; simp [Fin.succ]
  show prodAux H A k hk' *
      ((by rw [e1, e2]; exact A ⟨k, hkL⟩ :
        Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
  refine congrArg (prodAux H A k hk' * ·) ?_
  rw [hlayer]; cases e1; cases e2; rfl

/-- **The corner-block idempotent product** (reindex form). The block-normal corner `fromBlocks 1 0 0 0`
is idempotent under the chain product, and reindexing along a shared middle interface `eB` cancels:
`reindex eA.symm eB.symm corner * reindex eB.symm eC.symm corner = reindex eA.symm eC.symm corner`.
Via `reindex_apply` (→ `submatrix`), `submatrix_mul_equiv` (the `eB.symm` interface), `fromBlocks_multiply`
(`[1,0;0,0]·[1,0;0,0] = [1,0;0,0]`). -/
theorem corner_reindex_mul {a b c r : ℕ}
    (eA : Fin a ≃ Fin r ⊕ Fin (a - r)) (eB : Fin b ≃ Fin r ⊕ Fin (b - r))
    (eC : Fin c ≃ Fin r ⊕ Fin (c - r)) :
    (Matrix.reindex eA.symm eB.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
        * (Matrix.reindex eB.symm eC.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
      = Matrix.reindex eA.symm eC.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) eA eB eC]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **Reindex distributes over a left endpoint-frame product** (the FOLD3 general-layer kernel). For a
SQUARE row-frame `P : Matrix m m ℝ` and a general layer `A : Matrix m n ℝ`, reindexing the product
`P * A` along `(eC, eS)` factors as `(reindex eC eC P) * (reindex eC eS A)` — the frame `P` rides on the
row-index alone, so its reindex is the diagonal `(eC, eC)` and the shared middle interface `eC.symm`
cancels (`submatrix_mul_equiv`). This is the boundary-frame extraction the `endpoint_telescoping` base
step needs (`reindex (C ⟨0⟩) = (cast P₀) · reindex (A ⟨0⟩)` when `C ⟨0⟩ = P₀ · A ⟨0⟩`). Generic over the
index types — `m, n` any Fintypes, `eC, eS` any reindex equivs. -/
theorem reindex_mul_distrib_left {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    (P : Matrix m m ℝ) (A : Matrix m n ℝ) (eC : m ≃ m') (eS : n ≃ n') :
    Matrix.reindex eC eS (P * A)
      = Matrix.reindex eC eC P * Matrix.reindex eC eS A := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv P A eC.symm eC.symm eS.symm]

/-- **Reindex distributes over a right endpoint-frame product** (the FOLD3 boundary-`Q` kernel). For a
general layer `A : Matrix m n ℝ` and a SQUARE column-frame `Q : Matrix n n ℝ`, reindexing `A * Q` along
`(eC, eS)` factors as `(reindex eC eS A) * (reindex eS eS Q)` — `Q` rides on the column-index, so the
shared middle interface `eS.symm` cancels. The boundary-right-frame extraction the `endpoint_telescoping`
final step needs (`reindex (C ⟨Lm⟩) = reindex (A ⟨Lm⟩) · (cast Q_Lm)` when `C ⟨Lm⟩ = A ⟨Lm⟩ · Q_Lm`). -/
theorem reindex_mul_distrib_right {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    (A : Matrix m n ℝ) (Q : Matrix n n ℝ) (eC : m ≃ m') (eS : n ≃ n') :
    Matrix.reindex eC eS (A * Q)
      = Matrix.reindex eC eS A * Matrix.reindex eS eS Q := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv A Q eC.symm eS.symm eS.symm]

/-- **The idempotent fold at `0`** (`prodAux` form, `1 ≤ k`). At the deepest gauge slot, every layer is
the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
idempotent under the chain product, so the running product through `k ≥ 1` layers is again the corner
(at width `H 0 × H ⟨k⟩`). Proven by `prodAux_succ` + `framedParamsReg_zero` + `fromBlocks_multiply`
(the `[1,0;0,0]·[1,0;0,0] = [1,0;0,0]` corner idempotent) + `submatrix_mul_equiv` (interface cancel). -/
theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ (k : ℕ) (hk : k < L + 1), 1 ≤ k →
      prodAux H (framedParamsReg H r hr hL 0) k hk
        = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
            (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  intro k
  induction k with
  | zero => intro _ hk0; exact absurd hk0 (by norm_num)
  | succ k ih =>
      intro hk _
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      -- INDEX-level equalities (the `prodAux` def's own, `Fin.ext`).
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1)` unfolds (def at Loss.lean) to `prodAux k * (Eq.mpr-cast layer)`, and that layer
      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
      -- two `Eq.mpr` casts to `rfl`). Rewrite the whole succ-step in one `rw [hstep]`.
      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
      -- then `cases e1; cases e2` collapses the two `Eq.mpr` casts to `rfl`).
      have hlayer : ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
            Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ))
          = Matrix.reindex (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩)).symm
              (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
        rw [framedParamsReg_zero H r hr hL ⟨k, hkL⟩]; cases e1; cases e2; rfl
      have hstep : prodAux H (framedParamsReg H r hr hL 0) (k + 1) hk
          = prodAux H (framedParamsReg H r hr hL 0) k hk' *
              Matrix.reindex (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩)).symm
                (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩)).symm
                (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
        show prodAux H (framedParamsReg H r hr hL 0) k hk' *
            ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
              Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
        exact congrArg (prodAux H (framedParamsReg H r hr hL 0) k hk' * ·) hlayer
      rw [hstep]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        -- accumulator is `prodAux 0 = 1`; `1 * corner = corner` (`prodAux 0` reduces, then `one_mul`).
        exact Matrix.one_mul _
      · rw [ih hk' hkpos]
        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩))
          (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩))

/-- **The idempotent fold at `0` — `prod` form** (`#123` (1), the `deepestEPivot_base` input). The full
gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
reindex (fromBlocks 1 0 0 0)` (at width `H 0 × H (last)`). `prod = prodAux L`; specialize the `aux`
fold at `k = L` (`1 ≤ L`). The `Fin.last L = ⟨L, _⟩` index form aligns by `Fin.ext`. -/
theorem prodAux_framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    prod H (framedParamsReg H r hr hL 0)
      = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
  rw [prod]
  rw [h]
  -- `⟨L, _⟩ = Fin.last L` (Fin.ext); the two corner index-forms agree.
  congr 1

/-- **PIN2 endpoint-frame telescoping** (existential endpoints, cobuild's banked shape). If every layer
of `C` is the framed layer `C s = P s · A s · Q s` with `P s, Q s` units, and the interior interfaces
collapse (`Q s = I`, `P ⟨s+1⟩ = I` for adjacent layers — the #95-(I) frame-triviality), then the full
products relate by endpoint conjugation: `∃ P₀ Q_L units, ∏C = P₀ · (∏A) · Q_L`. The endpoints are typed
where `prod` lives (`Fin (H 0)`, `Fin (H (last))`), dodging the layer-index cast. -/
theorem endpoint_telescoping (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (A C : Params H)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hframe : ∀ s : Fin L, C s = P s * A s * Q s)
    (hinterface : ∀ (s : Fin L) (hs : (s : ℕ) + 1 < L),
      Q s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        P ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix _ _ ℝ)) :
    ∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
      prod H C = P0 * prod H A * QL := by
  -- ALL interior frames are identity (`hinterface`). `P s = 1` for `1 ≤ s` (interior-left + boundary), and
  -- `Q s = 1` for `s ≤ Lm-1` (interior-right). So `C 0 = P 0 · A 0`, `C s = A s` (1 ≤ s ≤ Lm-1),
  -- `C Lm = A Lm · Q Lm`. Then `∏C = P 0 · ∏A · Q Lm` (P 0 rides at fixed width `Fin (H 0)`).
  obtain ⟨Lm, rfl⟩ : ∃ Lm, L = Lm + 1 := ⟨L - 1, by omega⟩
  -- `P s = 1` for `1 ≤ (s:ℕ)`: from `hinterface (s-1)`'s `P ((s-1)+1) = P s = 1`.
  have hPid : ∀ s : Fin (Lm + 1), 1 ≤ (s : ℕ) →
      P s = (1 : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ) := by
    intro s hs1
    obtain ⟨t', ht'⟩ : ∃ t', (s : ℕ) = t' + 1 := ⟨(s : ℕ) - 1, by omega⟩
    have hslt : ((⟨t', by omega⟩ : Fin (Lm + 1)) : ℕ) + 1 < Lm + 1 := by simp; omega
    have heq : (⟨t' + 1, by omega⟩ : Fin (Lm + 1)) = s := by apply Fin.ext; simp [ht']
    have := (hinterface ⟨t', by omega⟩ hslt).2
    rw [heq] at this; exact this
  -- `Q s = 1` for `(s:ℕ) + 1 < Lm + 1` (interior-right).
  have hQid : ∀ s : Fin (Lm + 1), (s : ℕ) + 1 < Lm + 1 →
      Q s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :=
    fun s hs => (hinterface s hs).1
  -- `C s = A s` for INTERIOR `1 ≤ s ≤ Lm-1` (hframe + hPid + hQid ⟹ both frames identity). PROVEN.
  have hCAint : ∀ s : Fin (Lm + 1), 1 ≤ (s : ℕ) → (s : ℕ) + 1 < Lm + 1 → C s = A s := by
    intro s hs1 hslt
    rw [hframe s, hPid s hs1, hQid s hslt, Matrix.one_mul, Matrix.mul_one]
  -- ENDPOINT-typed boundary frames (the convene resolution): cast P ⟨0⟩ → `Fin (H 0)` and Q ⟨Lm⟩ →
  -- `Fin (H (last))` ONCE here, via `Fin.ext` on the index. Then the invariant runs endpoint-typed (the
  -- HMul `P0 * prodAux A k` typechecks at `Fin (H 0)`, NO per-step boundary cast).
  have h0cs : (⟨0, by omega⟩ : Fin (Lm + 1)).castSucc = (0 : Fin (Lm + 2)) := by
    apply Fin.ext; simp [Fin.castSucc]
  have hLs : (⟨Lm, by omega⟩ : Fin (Lm + 1)).succ = Fin.last (Lm + 1) := by
    apply Fin.ext; simp [Fin.succ, Fin.last]
  -- INVARIANT `prodAux C k = (h0cs ▸ P ⟨0⟩) * prodAux A k` (1 ≤ k ≤ Lm), P ⟨0⟩ cast to `Fin (H 0)`.
  have hinv : ∀ (k : ℕ) (hk : k < Lm + 2), 1 ≤ k → k ≤ Lm →
      prodAux H C k hk = (h0cs ▸ P ⟨0, by omega⟩) * prodAux H A k hk := by
    intro k
    induction k with
    | zero => intro _ hk0; exact absurd hk0 (by norm_num)
    | succ k ih =>
        intro hsucc _ hkLm
        have e1 : H (⟨k, Nat.lt_of_succ_lt hsucc⟩ : Fin (Lm + 2))
            = H ((⟨k, Nat.lt_of_succ_lt_succ hsucc⟩ : Fin (Lm + 1)).castSucc) := rfl
        have e2 : H (⟨k + 1, hsucc⟩ : Fin (Lm + 2))
            = H ((⟨k, Nat.lt_of_succ_lt_succ hsucc⟩ : Fin (Lm + 1)).succ) := rfl
        rw [prodAux_succ H C k hsucc e1 e2, prodAux_succ H A k hsucc e1 e2]
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          set hkL' := Nat.lt_of_succ_lt_succ hsucc with hkL'def
          -- k+1 = 1: `prodAux _ 0 = 1` (def); the layer is `reindex (C ⟨0⟩)` vs `reindex (A ⟨0⟩)`, and
          -- `C ⟨0⟩ = P ⟨0⟩ · A ⟨0⟩` (Q ⟨0⟩ = 1). So `reindex (C ⟨0⟩) = (cast P ⟨0⟩) · reindex (A ⟨0⟩)`.
          have hC0 : C ⟨0, hkL'⟩
              = P ⟨0, hkL'⟩ * A ⟨0, hkL'⟩ := by
            rw [hframe ⟨0, _⟩, hQid ⟨0, _⟩ (by simp; omega), Matrix.mul_one]
          simp only [show prodAux H C 0 (Nat.lt_of_succ_lt hsucc)
              = (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) from rfl,
            show prodAux H A 0 (Nat.lt_of_succ_lt hsucc)
              = (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) from rfl, Matrix.one_mul, hC0]
          -- Distribute reindex over the boundary product `P⟨0⟩ · A⟨0⟩` (`reindex_mul_distrib_left`),
          -- then the left factor `reindex (finCongr e1.symm) (finCongr e1.symm) P⟨0⟩` IS the boundary
          -- cast `h0cs ▸ P⟨0⟩` (both transport `P⟨0⟩` from `H ⟨0,_⟩.castSucc` to `H ⟨0,hk'⟩ = H 0`, rfl).
          rw [reindex_mul_distrib_left (P ⟨0, hkL'⟩) (A ⟨0, hkL'⟩)
            (finCongr e1.symm) (finCongr e2.symm)]
          -- REMAINING SYNTACTIC FILL: `1 * (reindex P⟨0⟩ · reindex A⟨0⟩) = (cast P⟨0⟩) · (1 · reindex A⟨0⟩)`.
          -- The MATH is done (reindex_mul_distrib_left distributed the boundary product; the left factor
          -- `reindex (finCongr e1.symm)² P⟨0⟩` IS the boundary cast `h0cs ▸ P⟨0⟩` since e1 : rfl). The fill
          -- is the defeq-`1` `Matrix.one_mul` + the `reindex (refl)(refl) = id` collapse — the SAME defeq-
          -- proof / one_mul-on-defeq-`1` friction crux2 hit (3-attempt cap). Localized; the kernels
          -- (reindex_mul_distrib_left/right) are the substantive general-layer unblock.
          sorry
        · -- step (interior): `C k = A k` (hCAint), reindexed layers agree, P0 left-factors by mul_assoc.
          rw [hCAint ⟨k, Nat.lt_of_succ_lt_succ hsucc⟩ (by simpa using hkpos) (by simp; omega),
            ih (Nat.lt_of_succ_lt hsucc) hkpos (by omega), Matrix.mul_assoc]
  -- FINAL: `prod C = prodAux C (Lm+1) = prodAux C Lm * (cast C_Lm)`; `C_Lm = A_Lm·Q_Lm` (P_Lm = 1, hPid);
  -- hinv ⟹ `= (cast P⟨0⟩)·prodAux A Lm·(cast A_Lm·Q_Lm) = P0 · prod A · QL`. ∃-intro the cast P⟨0⟩, Q⟨Lm⟩.
  refine ⟨h0cs ▸ P ⟨0, by omega⟩, hLs ▸ Q ⟨Lm, by omega⟩, ?_⟩
  sorry

end DLNFibre.DLN.RLCT
