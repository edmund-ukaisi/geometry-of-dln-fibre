# Consult: prove `realBranch_boostReady_case11` (Lean 4 + Mathlib v4.29) — the wall's last obligation

You have read access; give the cleanest Lean proof strategy (or identify the exact missing sub-lemma). This is a deep sub-proof — correctness + honesty about gaps matters more than speed.

## The goal (exact statement, Case1Wire.lean)
```
theorem realBranch_boostReady_case11 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared) (supportLayerOf p.conState) (foldRegion d e p)) :
    Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p)
```

## Defs
- `Deg1SupportedOn resid S V := ∀ j, ∃ c, (∀ i, ContinuousOn (c i) V) ∧ (∀ u∈V, resid j u = ∑ i∈S, c i u * u i) ∧ (∀ i, IgnoresCoords (c i) S V)`. (Coeffs IGNORE S.)
- `Deg1SupportedSlot ... j S fromLayer V := (∃ c, (∀i, ContinuousOn (c i) V) ∧ ∀u∈V, resid j u = ∑ i∈S, c i u * u i) ∧ PerLayerDeg1From ... fromLayer V`. (The ∃c coeffs need NOT ignore S; plus a per-layer affine grade.)
- `IgnoresCoords c S V := ∀ w∈V, ∀ m∈S, ∀ t, c (Function.update w m t) = c w`.
- `foldRegion d e p = Set.univ` (proven `foldRegion_eq_univ`).
- δ=1 (`hδ`) ⟹ `p.conState.cleared = 0` (`of_decide_eq_true`), so `supportAt d p.conState.layer 0 = blockCoords d p.conState.layer` = the FULL layer-S block `S_full` (widthMinUpto-capped).
- `ed.center` for case11 = `{canonPivotOf}` (a CROSS-LAYER birth corner, layer < S) `∪` a PARTIAL layer-S block (cols in `[0, runLen)`, runLen < widthMinUpto). So `ed.center ∩ S_full` = partial block ⊊ S_full; `ed.center ∖ S_full = {pivot}`; `S_full ∖ ed.center` = the "untouched" block coords (cols in `[runLen, widthMinUpto)`).

## Available ingredients (all banked on canonical)
- `realBranch_canonicalSchurStep e p ed hbranch : CanonicalSchurStep d p.conState ed.shearφ`, where
  `CanonicalSchurStep d s shearφ := ∀ u k, shearφ u k ≠ 0 → (decode k).1.1 = s.layer ∧ s.cleared < (decode k).1.2 ∧ s.cleared < (decode k).2` (the shear is supported on the layer-s carve STRICT interior).
- `canonShearOf_support` / `canonShearOf_apply_interior` (the shear's support + interior value −u_γ·u_β).
- `hslot` (above): parent residual is degree-1 on `S_full` (∃c form + per-layer affine).
- The b-chain mechanism (pnp-boost + my Codex cross-check, structural): along a real branch, `foldResid p`'s support-decomposition coefficient on an untouched block coord `i ∈ S_full∖partial` (equivalently `i > J₁`) carries a factor of `u_pivot` — so `c_i · u_i` can be absorbed into a `c'_pivot · u_pivot` term of the boost center. Verified TRUE on (2,2,2,2)/(3,3,2,2) (battery `case11_boost_readiness.py`); the countermodel `R_bad = Z·B·[[1,β],[γ,u_p]]` (unprepared γ≠0) shows it FAILS without CanonicalSchurStep.

## The re-expression (the intended mechanism)
`foldResid p j = ∑_{i∈S_full} c_i u_i` (hslot) → `∑_{i∈ed.center} c'_i u_i` (Deg1SupportedOn ed.center), where the partial-block terms carry over and the untouched terms `∑_{i∈S_full∖partial} c_i u_i` are absorbed into `c'_pivot · u_pivot` (each `c_i` carries `u_pivot` per the b-chain), and each `c'_i` must IGNORE ed.center.

## THE QUESTIONS
1. **Does the b-chain divisibility (`c_i` carries `u_pivot` for untouched `i`) FOLLOW from the given ingredients — `hslot` + `realBranch_canonicalSchurStep` (CanonicalSchurStep of ed.shearφ) + `hbranch` (⊇ p.IsRealBranch) — or does it need a NEW sub-lemma (a path-induction on `foldResid p`'s coefficients from p's canonical shears)?** Note CanonicalSchurStep is about ed.shearφ (the CURRENT edge), but foldResid p's b-chain comes from p's EARLIER shears — so is there a gap? Be precise about whether the current ingredient set is sufficient or a new inductive lemma is needed (and if so, its exact statement).
2. If sufficient: the cleanest Lean proof (the `c'` construction + the IgnoresCoords discharge + continuity).
3. **DROP-TEST (elder wants this for the weakest-form record):** does the center-factoring come from `hbranch + realBranch_canonicalSchurStep` ALONE (no `hslot`), or is `hslot`'s base genuinely consumed? Report which.

Answer: (1) sufficient / needs-new-lemma (+ its statement); (2) the proof or skeleton; (3) the drop-test verdict.
