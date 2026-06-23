import DLNFibre.DLN.RLCT.Foundations.Loss

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
  sorry

end DLNFibre.DLN.RLCT
