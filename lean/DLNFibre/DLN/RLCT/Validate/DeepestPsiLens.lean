import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiLens` — read-after-write lenses for the joint Ψ

The diffeo-bridge reparametrization Ψ (`hstep2`) acts on the last-layer core read `T1` (in the core
slot `q.2.1`, decoded by `paramsEquivFlat (deepestM)`) and the last-layer reg read `Y1` (in the
`(reg, spectator)` slots `(q.1, q.2.2)`, decoded by `regGaugeSlotEquiv` then `gaugeReadY`). To build Ψ as a
decode → edit → encode "lens" (Codex option A), the load-bearing facts are the **read-after-write
round-trips**: after re-encoding an edited `RegGaugeIdx → ℝ` function (resp. an edited core `Params`
tuple), `gaugeReadX/gaugeReadY/gaugeReadZ` (resp. the per-layer core decode) return the edited value at the touched
tag and the original value elsewhere.

This module records those round-trips. They are the `Equiv.apply_symm_apply` / `symm_apply_apply`
identities specialized to the slot decoders — the cheap de-risking step Codex flagged (the index-cast
trap is here, not in slot overlap). Sorry-free; axiom-clean.

The "write" is just function re-encoding: a Ψ that produces `(reg', spec') := regGaugeSlotEquiv.symm g'`
and `core' := paramsEquivFlat (deepestM) t'` reads back as `gaugeReadY (reg', spec') = (g' at the Y-tag)` and
`coreDecode core' = t'`. No interleaving subtlety: `regGaugeSlotEquiv` un-flattens BOTH `q.1` and `q.2.2`
into ONE `RegGaugeIdx → ℝ` function, so a single re-encode handles both slots together.
-/

open Matrix
open scoped BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **Reg-gauge read-after-write (X tag).** `gaugeReadX` of the `(reg, spec)` slot re-encoded from a
`RegGaugeIdx → ℝ` function `g` returns `g` at the X-tag `⟨s, inl (inl (i,j))⟩`. -/
theorem gaugeReadX_regGaugeSlotEquiv_symm (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (g : RegGaugeIdx H r → ℝ) (s : Fin L) (i j : Fin r) :
    gaugeReadX H r hr hL ((regGaugeSlotEquiv H r hr hL).symm g) s i j
      = g ⟨s, Sum.inl (Sum.inl (i, j))⟩ := by
  simp only [gaugeReadX, Matrix.of_apply]
  rw [(regGaugeSlotEquiv H r hr hL).apply_symm_apply]

/-- **Reg-gauge read-after-write (Y tag).** `gaugeReadY` of the re-encoded `(reg, spec)` slot returns `g` at
the Y-tag `⟨s, inl (inr (i,j))⟩`. (The last-layer Y-tag is the one the joint Ψ edits.) -/
theorem gaugeReadY_regGaugeSlotEquiv_symm (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (g : RegGaugeIdx H r → ℝ) (s : Fin L) (i : Fin r) (j : Fin (H s.succ - r)) :
    gaugeReadY H r hr hL ((regGaugeSlotEquiv H r hr hL).symm g) s i j
      = g ⟨s, Sum.inl (Sum.inr (i, j))⟩ := by
  simp only [gaugeReadY, Matrix.of_apply]
  rw [(regGaugeSlotEquiv H r hr hL).apply_symm_apply]

/-- **Reg-gauge read-after-write (Z tag).** `gaugeReadZ` of the re-encoded `(reg, spec)` slot returns `g` at
the Z-tag `⟨s, inr (i,j)⟩`. -/
theorem gaugeReadZ_regGaugeSlotEquiv_symm (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (g : RegGaugeIdx H r → ℝ) (s : Fin L) (i : Fin (H s.castSucc - r)) (j : Fin r) :
    gaugeReadZ H r hr hL ((regGaugeSlotEquiv H r hr hL).symm g) s i j
      = g ⟨s, Sum.inr (i, j)⟩ := by
  simp only [gaugeReadZ, Matrix.of_apply]
  rw [(regGaugeSlotEquiv H r hr hL).apply_symm_apply]

/-- **Core read-after-write.** The per-layer core decode of a re-encoded core slot
`paramsEquivFlat (deepestM) t'` returns the edited tuple `t'` at every layer. (The joint Ψ edits the
last-layer core block; this reads it back.) -/
theorem coreDecode_paramsEquivFlat (H : Fin (L + 1) → ℕ) (r : ℕ)
    (t' : Params (deepestM H r)) (s : Fin L) :
    (paramsEquivFlat (deepestM H r)).symm (paramsEquivFlat (deepestM H r) t') s = t' s := by
  rw [(paramsEquivFlat (deepestM H r)).symm_apply_apply]

/-- **The reg-gauge edit is a clean function update at a single tag** (the `RegGaugeIdx → ℝ` level): if
`g'` agrees with `g` off a tag set and equals the new value on it, then `gaugeReadX/Y/Z` of the re-encode
read the new value on the touched tag and the old value elsewhere — directly from the read-after-write
lemmas + `g' = Function.update …`. This is the form the Ψ's E2 reg-preservation consumes (only the
last-layer Y-tag changes; all other tags, hence `gaugeReadX`, `gaugeReadZ`, and `gaugeReadY` at non-last layers, are
fixed). -/
theorem gaugeReadY_regGaugeSlotEquiv_symm_update_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (g : RegGaugeIdx H r → ℝ) (tag : RegGaugeIdx H r) (v : ℝ)
    (s : Fin L) (i : Fin r) (j : Fin (H s.succ - r))
    (hne : (⟨s, Sum.inl (Sum.inr (i, j))⟩ : RegGaugeIdx H r) ≠ tag) :
    gaugeReadY H r hr hL ((regGaugeSlotEquiv H r hr hL).symm (Function.update g tag v)) s i j
      = gaugeReadY H r hr hL ((regGaugeSlotEquiv H r hr hL).symm g) s i j := by
  rw [gaugeReadY_regGaugeSlotEquiv_symm, gaugeReadY_regGaugeSlotEquiv_symm, Function.update_of_ne hne]

end DLNFibre.DLN.RLCT
