/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Embedding
import DLNFibre.DLN.RLCT.Foundations.Loss

set_option linter.style.longLine false

/-!
# `RouteMSJDeepIndex` — the finite CR-tree path index (deep atlas, Tide B §3.1)

**Thread `genm-deepatlas`, aoyagi-full Stage 2 (branch β, NATIVE).** The finite index of the deep
stratified-resolution atlas (`genm-deepatlas-design/design.md` §3.1): one flat dependent `Σ`-tree
enumerating the root-to-leaf paths of the composite-rank recursion. Design locked by the
`gluing-shape` Codex pass — a single flat `Fintype` fed once to the banked null-overlap gluing (nested
per-level unions gain nothing).

## The path type

`CRPath H s j hj q` is a path through the CR recursion starting from an effective chain of length `j`
with a right-factor width `q`. Each descent node records:
- the exact effective rank `r ≤ min (H⟨k⟩) q` at this level,
- a row pivot `ρ : Fin r ↪ Fin (H⟨k⟩)` and a column pivot `κ : Fin r ↪ Fin q` (the size-`r` nonsingular
  minor selecting the big-cell),
- the tail path on the shortened chain with new width `r`.
The terminal node (`j = 0`, the reduced product is `1`) carries the rank constraint `q ≤ s`.

`CRIndex H s := CRPath H s L le_rfl (H (Fin.last L))` is the index of the full chain (start width
`H (last)`, the input dimension). It is a `Fintype` (finite branching × bounded depth).

## What lands here (sorry-free)

* **`CRPath`** — the dependent `Σ`-tree path type (recursion on the level).
* **`instFintypeCRPath` / `CRIndex`** — the finite index. `Fintype` is noncomputable (via
  `Function.Embedding.fintype`), which is fine — the index is a proof-level enumeration, not executed.

The cells and coverage set-equality (§3.2) + the thin generic-`f` gluing wrapper (§3.3) build on this.
Measurability defers to the loss tide (the banked gluing lemma needs none). Axiom target
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix

namespace DeepAtlas

/-- **The CR-tree path type.** A root-to-leaf path of the composite-rank recursion, from an effective
chain of length `j` with right-factor width `q`. A descent node picks the exact effective rank `r`, a
size-`r` row pivot into the level-`k` width `H⟨k⟩`, a size-`r` column pivot into `q`, and the tail on
the shortened chain of width `r`; the terminal node carries `q ≤ s`. -/
def CRPath {L : ℕ} (H : Fin (L + 1) → ℕ) (s : ℕ) : (j : ℕ) → j ≤ L → ℕ → Type
  | 0, _, q => PLift (q ≤ s)
  | (k + 1), hk, q =>
      Σ r : Fin (min (H ⟨k, by omega⟩) q + 1),
        (Fin r.1 ↪ Fin (H ⟨k, by omega⟩)) × (Fin r.1 ↪ Fin q) × CRPath H s k (by omega) r.1

/-- The CR-tree path type is a `Fintype`: bounded branching (finitely many ranks × pivot embeddings per
node) and depth `≤ L`. Noncomputable via `Function.Embedding.fintype`. -/
noncomputable instance instFintypeCRPath {L : ℕ} (H : Fin (L + 1) → ℕ) (s : ℕ) :
    ∀ (j : ℕ) (hj : j ≤ L) (q : ℕ), Fintype (CRPath H s j hj q)
  | 0, _, q => by unfold CRPath; infer_instance
  | (k + 1), hk, q => by
      unfold CRPath
      haveI : ∀ r : Fin (min (H ⟨k, by omega⟩) q + 1), Fintype (CRPath H s k (by omega) r.1) :=
        fun r => instFintypeCRPath H s k (by omega) r.1
      infer_instance

/-- **The deep-atlas finite index.** The CR-tree paths of the full chain (start width `H (last)`, the
input dimension) — the finite family the atlas cells are indexed by and the null-overlap gluing
consumes once. -/
noncomputable def CRIndex {L : ℕ} (H : Fin (L + 1) → ℕ) (s : ℕ) : Type :=
  CRPath H s L le_rfl (H (Fin.last L))

noncomputable instance {L : ℕ} (H : Fin (L + 1) → ℕ) (s : ℕ) : Fintype (CRIndex H s) :=
  instFintypeCRPath H s L le_rfl (H (Fin.last L))

/-- Non-vacuity: the terminal (length-`0`) path is inhabited exactly when the width fits under `s`
(`q ≤ s`), so the index is not vacuously empty at a reachable leaf. -/
example {L : ℕ} (H : Fin (L + 1) → ℕ) (s q : ℕ) (hq : q ≤ s) :
    Nonempty (CRPath H s 0 (Nat.zero_le _) q) :=
  ⟨(by unfold CRPath; exact PLift.up hq)⟩

end DeepAtlas

end DLNFibre.DLN.RLCT
