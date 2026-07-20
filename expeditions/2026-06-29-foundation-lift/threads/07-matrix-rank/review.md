# Decorrelated review — P2-R2 matrix minor-rank core (`Core.Matrix.RankMinors`)

**Reviewer:** independent (read-only, no full build, decorrelated + Codex consult).
**Target:** `lean/DLNFibre/Core/Matrix/RankMinors.lean` (extracted core) + `lean/DLNFibre/Core/RankLocusClosed.lean` (DLN remainder).
**Branch/worktree:** `expedition/foundation-lift-p2`, worktree `…/foundation-lift`. The dispatch named HEAD `09c5cb79`; the worktree HEAD has since advanced to `28f8ff3a` and the extraction commit is `eff28654` — `RankMinors.lean` is **byte-for-byte identical** to its content at the extraction commit (`diff` clean), so the review is on the same artefact.

## Overall verdict: **PASS** — clear to PR (no blocking findings)

All three crux items survive. The `←` direction is sound at the stated `Fin`/`ℕ` generality, with no wrong index/card step; the re-home is faithful (proof bodies code-identical modulo the forced qualifier drop); the split is faithful (DLN remainder signatures identical, names match content). One non-blocking honesty note on the deferred generalization (it is an honest non-extension, not a hidden narrowing). The Codex decorrelated read independently confirmed soundness.

---

## Item (1): `rank_le_iff_forall_submatrix_det_eq_zero` — the `←` direction — **PASS**

The `←` (`minors vanish ⟹ rank ≤ r`, contrapositive via `exists_submatrix_det_ne_zero_of_le_rank`) is **sound**, and the headline `↔` matches name=content over a field.

**Lemma chain verified against Mathlib v4.29** (all exist with the used signatures):
- `Matrix.cRank_submatrix_le`, `cRank_toNat_eq_rank`, `cRank_le_card_width` — back `rank_submatrix_le_rank` (the `ℕ`-cast). FACT.
- `Matrix.rank_of_isUnit (A) : A.rank = Fintype.card n` — backs `det_eq_zero_of_rank_lt`. FACT.
- `LinearIndependent.rank_matrix : LinearIndependent k M.row → M.rank = Fintype.card m` — gives `B.rank = r+1`. FACT.
- `Matrix.rank_transpose [Field] [Fintype m] : Aᵀ.rank = A.rank` — gives `r+1 ≤ Bᵀ.rank`. FACT.
- `exists_linearIndependent' v : ∃ κ a, Injective a ∧ span(range (v∘a)) = span(range v) ∧ LinearIndependent (v∘a)` + `finrank_span_eq_card` + `rank_eq_finrank_span_row` — give `Fintype.card κ = A.rank`. FACT.
- `Function.Embedding.nonempty_of_card_le` (`Data/Fintype/EquivFin.lean`) — the `Fin s ↪ κ` slice. FACT.
- `Matrix.linearIndependent_cols_iff_isUnit {A : Matrix m m K}` (square, field) + `isUnit_iff_isUnit_det` — the square block `C` is a unit ⟹ `det ≠ 0`. FACT (both square+field; `C : Matrix (Fin (r+1)) (Fin (r+1)) k`).

**Index / `Fintype.card_fin` steps — all three correct** (the brief's flagged risk):
- `RankMinors.lean:69` — `rank_of_isUnit` ⟹ `A.rank = card(Fin p)`; `card_fin` ⟹ `= p`; `omega` vs `A.rank < p`. OK.
- `RankMinors.lean:102` — discharges `card(Fin s) ≤ card κ` (= `s ≤ card κ = hsle`) for the embedding. OK.
- `RankMinors.lean:127` — `rank_matrix` ⟹ `B.rank = card(Fin (r+1))`; `card_fin` ⟹ `= r+1`. OK.

**The one fragile step — the column identity (line 133)** `C.col = fun i ↦ Bᵀ.row (ec i)` — is genuinely true, not just plausible: with `C = A.submatrix er ec`, `B = A.submatrix er id`, one has `C.col j i = A (er i) (ec j) = B i (ec j) = Bᵀ.row (ec j) i`. The row set `er` is fixed before `B` and reused for `C`, so the square block whose columns were shown independent is exactly `C` — no block drift. No circularity: the `←` proof does not invoke the criterion being proved. The `r+1 ≤ p` / `r+1 ≤ q` bounds are discharged internally by the produced injections (no missing hypothesis). **Codex (xhigh, decorrelated) independently reached the same verdict (`sound`)**, flagging the column identity as the only fragile point and confirming the indices line up (`codex/hard-direction-{prompt,answer}.md`).

**Honesty on the `↔`:** the criterion is stated with *arbitrary* index maps `er, ec` (no injectivity demanded of the caller); the `→` is unweakened by non-injective selections (a repeated row/column ⟹ `det = 0`), and the `←` *produces* injective witnesses, existentially packed in `exists_submatrix_det_ne_zero_of_le_rank` — not part of the `↔`. `[Field k]` only; no algebraic-closedness or `Nontrivial` smuggled in. Name = content.

**Deferred `Fintype`-index generalization — honest non-extension (non-blocking).** The statement is `Matrix (Fin p) (Fin q) k` with `{p q r : ℕ}`; the general-`Fintype` index was considered and *not* adopted. This is a faithful record, not a hidden narrowing: (a) the pre-extraction source was **already** at exactly this `Fin`/`ℕ` generality (verified by diff below), so no prior claim is weakened; (b) the DLN consumers all index by `Fin (d j)` / `Fin (d i)`, so the `Fin` shape is what they need. The follow-up is a clean upstream-grade widening, not a gap in the stated claim.

## Item (2): `rank_map_eq_of_injective` — **PASS**

Statement: for `[Field R] [Field S]`, injective `ι : R →+* S`, `(B.map ι).rank = B.rank`. Proof: per-`r` the determinantal criterion transfers each minor via `Matrix.submatrix_map` + `RingHom.map_det` + `map_eq_zero_iff ι hι`, then `le_antisymm`. Sound.

**Re-home is faithful.** Code-only diff of the proof body, pre-extraction (`RankLocusClosed` lines 353–364, in a separate `namespace Matrix` block) vs current (`RankMinors` 163–173): **the only change is the two `rw` references** dropping the `DLNFibre.Core.` qualifier (`DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero` → `rank_le_iff_forall_submatrix_det_eq_zero`), forced by the namespace co-location and logic-neutral now that both lemmas share `namespace Matrix`. Statement, hypotheses (two distinct fields `R, S`), and all other proof steps identical.

## Item (3): Faithful split — **PASS**

**Core six lemmas** (`rank_submatrix_le_rank`, `det_eq_zero_of_rank_lt`, `submatrix_det_eq_zero_of_rank_le`, `exists_injective_linearIndependent_rows`, `exists_submatrix_det_ne_zero_of_le_rank`, `rank_le_iff_forall_submatrix_det_eq_zero`): code-only diff pre-extraction vs `RankMinors` = **IDENTICAL** (71 code lines each, zero diff). Docstring `Direction A/B` renamed to `→`/`←` — cosmetic, name-neutral.

**DLN remainder stayed local in `RankLocusClosed`** and signatures are **identical** pre vs post extraction for all ten (`eval_submult_genericTuple`, `minorPoly`, `eval_minorPoly`, `rankMinorSet`, `mem_zeroLocus_rankMinorSet_iff`, `image_orbitRankLocus_eq_zeroLocus`, `isZariskiClosed_orbitRankLocus`, `orbit_subset_orbitRankLocus`, `orbitSet_subset_orbitRankLocus`, `vanishingIdeal_orbitRankLocus_le_orbitSet`). No statement drift; names match content (e.g. `isZariskiClosed_orbitRankLocus` proves closedness via `image_…_eq_zeroLocus` + Galois `l_u_l_eq_l`; `minorPoly` is a det, named as a polynomial — correct).

**Wiring** (read-only checks, no build): `DLNFibre.lean:498` appends `import DLNFibre.Core.Matrix.RankMinors`; `RankLocusClosed.lean:4` imports it; in-namespace references resolve via `open Matrix` (`RankLocusClosed:118,129,196,204`; Core consumers `DeterminantalChartRing:303`, `FibreRankBridge:113,204`). **No stale `DLNFibre.Core.`-qualified copy of any of the seven names survives.** `RankMinors` is `[Field k]` only. No `sorry`/`axiom`/`native_decide`/`#exit` in either file.

---

## Notes (non-blocking)
- I did **not** run a build (per the read-only / phase-boundary gate; a P2-R3 formaliser is writing `GraphIdealHeight` concurrently). The statement card reports green at 3820 jobs, axiom-clean `[propext, Classical.choice, Quot.sound]`; this review verifies the *content/soundness* and *faithfulness of the re-home*, not a fresh build.
- The deferred `Fintype`-index generalization (item 1) is recorded honestly and is a legitimate clean follow-up — recommend it be carried in the roadmap, not the PR.

**Artefacts:** `codex/hard-direction-prompt.md`, `codex/hard-direction-answer.md` (decorrelated soundness consult, verdict `sound`).
