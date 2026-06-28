# KC1 unified soundness-sketch — front-align `deepestPoint_exists` (boundary layers)

**Status:** sketch for controller review BEFORE the re-proof (the soundness gate on re-opening the
banked `deepestPoint_exists`/:337 proof). **Verdict: ADDITIVE — NOT the STOP** (Codex xhigh
decorrelated, `codex/unified-answer.md`).

The one unified change: strengthen `deepestPoint_exists` to emit a deepest point whose **boundary
layers are front-pivot-aligned** — layer-0's leading `r×r` block invertible (KC1) AND the last layer's
front-`r` columns a pivot set (KC2) — and carry both as **additive `IsDeepLayers` conjuncts**. This
discharges the gauge producer's `hJfront` (KC2) and the (1a) invertible-corner (KC1) on the
*constructed* deepest point, collapsing the two entangled kill-conditions into one edit.

## The key structural fact (source-verified)

`deepestPoint_exists` (r>0, L≥2) does NOT bake in `block_elimination`'s bases. It:
1. calls `block_elimination B` → units `P,Q` with `P·B·Q = corner`;
2. sets `U := P⁻¹·embM` (a×r), `V := projM·Q⁻¹` (r×b), notes `B = U·V` (`factor_from_blockElim`),
   `rank U = rank V = r`;
3. builds the deepest point as `wLayers H r U V` (layer0 `= U·projM`, last `= embM·V`, interiors `corM`).

**`wLayers`, `prod_wLayers_ge2` (prod = U·V = B), and every existing `IsDeepLayers` conjunct
(`deepestPoint_isDeep`'s 5 parts) are proved for ARBITRARY `U,V` with `B = U·V`, `rank U = rank V = r`.**
They never read `block_elimination`'s internal bases. `block_elimination` is used ONLY to produce one
factorization at step (2).

## (a) The frame choice / aligned factorization

Front-alignment is a property of `U,V`:
- layer0 `= U·projM` ⟹ leading `r×r` block = top-`r` rows of `U`. **KC1 ⟺ `U`'s top `r` rows independent.**
- last layer `= embM·V` ⟹ front-`r` cols = front-`r` cols of `V`. **KC2 ⟺ `V`'s front `r` cols independent.**

Pure basis-ordering inside `block_elimination` does NOT control these (leading-minor invertibility is a
subspace-position property, not basis-orderable — sympy-checked + Codex-confirmed). The alignment is
supplied two ways, combined:
- **Existence of an aligned factorization** for a front-aligned `B`: a NEW lemma
  `∃ U V, B = U·V ∧ rank U = rank V = r ∧ (U top-r rows indep) ∧ (V front-r cols indep)` — built from a
  chosen basis matrix of `col(B)` whose leading `r×r` minor is invertible (and dually for `row(B)`).
- **Row+column permutation WLOG at the HEADLINE** brings a general `B` into the front-aligned position
  (`rlct_infimum_rowPerm_eq` [NEW, mirror of the banked `rlct_infimum_colPerm_eq`] + the banked colPerm).
  General position vs the first `r` coords is *exactly* the front-pivot condition the permutations achieve
  (Codex Q2). KC2's colPerm half is already landed (`headline_frontPivot_exists`, c7c8e2ed).

`deepestPoint_exists` then uses the aligned `(U,V)` (from the existence lemma) in place of
`block_elimination`'s `.choose` factorization — supplying `U,V` to the already-`U,V`-parametric `wLayers`.

## (b) Additivity at :337 (the soundness argument)

`block_elimination` / `hSigma` / the `bKer`/`bDomS`/`quotKerEquivRange`/`Sigma` decomposition are
**reused VERBATIM or bypassed — never re-proved**:
- The aligned `(U,V)` comes from a SEPARATE factorization-existence lemma, not from re-deriving
  `block_elimination` with bespoke bases. So `hSigma`'s proof logic is untouched (Codex Q1: YES).
- Existing `IsDeepLayers` conjuncts (prod=B; per-layer rank r; interior=corM; layer0 last-cols-zero;
  last-layer last-rows-zero) all still hold for the aligned `(U,V)`: the zero-shapes come from
  `projM`/`embM` (B-independent), rank from `rank U`/`rank V`, interior `corM` is U,V-independent
  (Codex Q3: YES).
- The 2 new conjuncts are additive ∧-clauses provable from "U top-r rows indep" / "V front-r cols indep"
  (Codex Q4: YES; one mechanical note — projection paths need updating if `IsDeepLayers` stays a nested
  `∧`; cosmetic, not soundness).

## (c) Codex verdict (xhigh, decorrelated — `codex/unified-answer.md`)

All five questions: ADDITIVE. "No place in supplying aligned `U,V` forces re-proving `hSigma` or the
kernel/range/Sigma decomposition." Q2 nuance: "general position" = the front-pivot condition the
row/col permutations achieve, not a stronger genericity.

## Build plan (after green-light)

1. `rlct_infimum_rowPerm_eq` — NEW, mirror of banked colPerm (heavier: first-layer row peel rides the
   whole `prodAux` fold). LEAF-SAFE, no :337.
2. Aligned-factorization existence lemma (`Basis`/pivot-selection; the leading-minor argument).
3. Strengthen `IsDeepLayers` (+2 conjuncts) + `deepestPoint_exists` to use the aligned `(U,V)` and emit
   them. **block_elimination/:337 reused, NOT re-proved.** Update consumers' projection paths (mechanical).
4. J-parametric producer plumbing: replace the `.choose` at `DeepestGaugeConstruction:2996/2998`; discharge
   `hJfront` (2939/3301) from the new last-layer-pivot conjunct.
5. Headline: row+col WLOG → aligned Bp → the landed `aoyagi_learning_coefficient_frontPivot`.

LoC estimate: rowPerm ~120-180; factorization existence ~60-100; IsDeepLayers/deepestPoint strengthening
+ consumer updates ~80-150; producer plumbing ~40-80. STOP trigger (unchanged): if step 3's emission
forces re-proving `hSigma` (it should not, per the above) → STOP+report.
