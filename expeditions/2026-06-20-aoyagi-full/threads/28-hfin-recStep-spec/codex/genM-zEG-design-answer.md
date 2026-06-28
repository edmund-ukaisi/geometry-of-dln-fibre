Q1. **(a).** The generic bijection is the bulk, but carve on the normalized off-pivot cell subtype and use `piRatioG` only as the outer decoder from `Fin N`. Define with `m` and ambient `Fin (m+1)` if possible:
`inl (a,b) ↦ (a.succ,b.succ)`, `inr (inl a) ↦ (a.succ,0)`, `inr (inr b) ↦ (0,b.succ)`.
Then compose `Fin N ≃ {off-pivot flat cells}` with this cell carve. This keeps readback cell-native: after one decoder lemma, the M22/g/b lemmas are about actual cells, not arithmetic slots. `MeasurableEquiv.piCongrLeft`, `MeasurableEquiv.sumPiEquivProdPi`, `volume_measurePreserving_piCongrLeft`, `volume_measurePreserving_sumPiEquivProdPi`, `Fin.succAbove_ne`, `Fin.exists_succAbove_eq`, and `finSumFinEquiv` are CONFIRMED in the local v4.29 checkout.

Q2. Yes: prove three class readbacks, then assemble entrywise. The target lemmas should be:
`R' a.succ b.succ = M22part (a,b)`,
`R' a.succ 0 = gpart a`,
`R' 0 b.succ = bpart b`.
Then `ext a b; simp [ScG, matOfG, bgShiftG, Matrix.sub_apply, ...]` should close the identity. A “slick” matrix-level identity will still need these same entries, but with worse rewriting opacity. The real cast risk is `Fin (r-1) → Fin r`; mitigate by proving the carve for `Fin (m+1)` and only casting once at the boundary.

Q3. Confirmed mathematically: with pivot normalization, `M11` is exactly the `1×1` matrix `[1]`, so its inverse is exactly `[1]`, and `M21 · M12` is exactly `fun a b => M21 a 0 * M12 0 b`. Lean-wise, avoid `Matrix.inv` here if you can. Use the explicit `j = 1` formula, or feed `Minv := fun _ _ : Fin 1 => 1` into the repo’s `schur_key_identity`; the left-inverse proof is a `Fin 1` simp/ext proof. If forced through `Matrix.inv`, prove a local `by ext i j; fin_cases i; fin_cases j; simp [M11]` lemma rather than depending on global inverse simplification.

Q4. No. The generic `zEG` carving/readback has no new design gap beyond volume reshape plus finite-index bookkeeping. The outer product shape, M22 indexing, bounded shift `|g a * b b'| ≤ 1`, Tonelli with bg outermost, and per-fixed-bg translation all generalize. The sharp remaining gap is outside this sub-step: the later per-`z` N2b + Morse-peel positivity/glue in `schurRatioResidGen_mid`, not `Sc = M22 - Sh(rest)`.

Q5. Top risk 1: `Fin (r-1)`/`Fin r` cast churn around successors and `(0,0)` exclusion. Mitigation: implement the carve in `m` with ambient `Fin (m+1)`, and expose only three readback lemmas.

Top risk 2: bijection orientation/cardinality noise between `Fin N`, off-pivot subtype, and nested sums. Mitigation: make `Fin N ≃ offPivotSubtype` a separate decoder equivalence, then compose with a subtype carve; use nested `(Fin m × Fin m) ⊕ (Fin m ⊕ Fin m)` and split by `sumPiEquivProdPi`.

GENERIC-zEG: PURE-VOLUME; CARVE-ON: subtype