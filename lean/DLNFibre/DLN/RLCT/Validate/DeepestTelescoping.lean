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
  -- NOT NEEDED for L2/PIN2 (controller verdict (a) 2026-06-23): L2 light-(iii) + PIN2 loss_squeeze
  -- close via the two-sided BOUND (rlctAtOn_squeeze ← fullProduct_loss_squeeze, scalar/gauge-block,
  -- cast-free), NOT this exact equality. Kept as the STRONGER-but-unneeded result. With prodAux_succ
  -- now PROVEN (above), the remaining induction is a generalized prodAux-depth invariant +
  -- interface-cancellation (Q s · P (s+1) = 1) + endpoint cast-extraction, traversed by
  -- `Matrix.submatrix_mul_equiv` — a known-shape multi-step induction (formaliser-hours), not a wall.
  -- Left as a sorry'd building block; build it if the exact equality is ever wanted (it is not, for
  -- the critical path D1∘L2). The one-pass that PROVED prodAux_succ closed the cast-bridgeability
  -- question; this is the orthogonal fold-assembly.
  sorry

end DLNFibre.DLN.RLCT
