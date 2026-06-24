# thread 14 — G2-3 total-presentation design recon (G2-3a, explore/scout — scope the wall)

**Type:** explore (scout) · design recon. G2-2 (the localized BASE presentation `A_loc/Iad ≅ₐ[k] Sd`)
is done. G2-3 is the genuine wall: the **total**-space side + flatness, en route to
`codim_{Σ̄^r}(fibre) = δ` ⟹ the final `codimRepCanonical(fibre d B) = cCodim d r + r(d_0+d_N−r)`. Scope
it before any formaliser tide. **No production Lean** (throwaway probes fine); output = the G2-3
rung-ladder + reachability verdict. Decorrelated Codex required.

## The target + where G2-2 leaves us
Final Core target (= `BundleShiftInterface.cited_bundle_shift`): for `[Field K][IsAlgClosed K][CharZero K]`,
`B.rank = r`, `r ≤ d k'`, `0 < N`:
`codimRepCanonical (fibre d B) = codimRepCanonical (productRankLocusLE d r) + (r*(d_0+d_N−r):ℕ∞)`
(= `cCodim d r + δ`; Brick A gives `codimRepCanonical Σ̄^r = cCodim`). Via the catenary this is
`codim_{Σ̄^r}(fibre) = δ`. G1 (reduce-to-`E`) lets us work at the normal form `E = diag(I_r,0)`.

**Landed foundation (reuse, don't rebuild):** G2-2's base presentation `A_loc/Iad ≅ Sd` (regular dim δ,
`height Iad = C`); the reusable engines — `MvPolynomialKerAeval` (`ker_aeval = graphIdeal`),
`GraphIdealHeight` (`height_graphIdeal_eq` + localized transport), `DeterminantalBaseElimination`
(reindex + `blockAlgEquiv` + detΔ bridge), `DeterminantalChartRing` (bordered Schur minor); the
going-down height-additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (LANDED in
Mathlib, used in `FlatQuasiFiniteHeight`/`PolynomialDimension`); the affine-domain equidim + the
catenary bridge.

## Questions to answer (the blueprint)
1. **The total-space presentation on the chart.** `B_total` = the coordinate ring of `Σ̄^r ⊆ Rep_d` (vs
   G2-2's base `Mat^{rk=r}`). On the pivot chart, does the reindex/graph-ideal/Schur machinery extend
   from `Mat` to the full `Rep_d`? What are the "free" vs "forced" coordinates of the TOTAL ring on the
   chart, and what is the fibre-over-`E` coordinate ring `F_E` concretely (the "zero-product-type"
   locus)? Is `B_loc ≅ A_loc ⊗_k F_E` (the bundle trivialization) the right object, or is there a
   cheaper route reusing G2-2?
2. **Flatness / going-down.** The chain needs `HasGoingDown` for the comorphism `A_base → B_total` ON
   THE CHART (mult is NOT globally flat — fibre dim jumps). Does `B_loc ≅ A_loc ⊗ F_E` (free over
   `A_loc`) ⟹ flat ⟹ going-down, with the landed `height_eq_height_add_…`? Pin the exact lemma chain to
   `codim_{Σ̄^r}(fibre) = δ`. (Reserve: Codex's earlier "total-coordinate" route — fibre = `C+δ` explicit
   coordinate equations on the chart ⟹ height directly, no going-down — evaluate if cleaner now.)
3. **Reducibility (the G2-5 question).** `codimRepCanonical = iInf` over minimal primes; Σ̄^r reducible
   when θ>1. How do the fibre's components match Σ̄^r's orbit-components (Brick A
   `minimalPrimes_sigmaIdeal_eq`) with the uniform `+δ`? Pin the correspondence; decide whether it folds
   into G2-3 or stays a separate rung.
4. **Rung-ladder + risk.** Decompose G2-3 (+G2-4/G2-5) into tide-sized rungs; per rung the machinery
   (reuse-vs-new), size, risk; name the single hardest sub-wall and its reachability verdict. Is the
   total-presentation a clean mirror of G2-2's base presentation, or materially harder (Rep_d ≫ Mat)?

## Method / rules
Exact algebra; use the `(2,2,2),r=1` anchor (`dim Σ̄^1 = 7 = 3 + 4`; fibre codim `4 = C(1)+δ(3)`). **Fire a
decorrelated `local-codex-consult`** (authenticated, xhigh) on Q1+Q2 (the total presentation + flatness),
saved under `threads/14-total-presentation-design/codex/`. Read: `Core/DeterminantalBasePresentation`
(G2-2), `Core/DeterminantalBaseElimination`, `Core/MultComorphism`/`FibreCodim` (the fibre + comorphism),
`Core/SigmaCodim` (Brick A + minimal primes), `Core/FlatTrivialProductProbe`/`ChartFlatnessProbe` (the
flatness API + the prior NO-GO write-ups). **NO production Lean / no commits to library files.**

## Output (report to controller)
The confirmed G2-3 rung-ladder, per-rung machinery + size + risk, the single hardest sub-wall + its
reachability verdict, the decorrelated-Codex read, and a clear recommendation: the route for the total
presentation + flatness (or, if the total presentation is out of reach at v4.29, the precise wall + the
fallback). Honest scout — if G2-3 is genuinely much harder than G2-2 (or a wall), say so plainly.
In-repo notes only; never `~/.claude/**/memory/`; don't touch other worktrees.
