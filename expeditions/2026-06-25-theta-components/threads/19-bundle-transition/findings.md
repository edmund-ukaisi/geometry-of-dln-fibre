# Thread 19 — bundle transition cocycle (B3-3) (formaliser) — certificate

**Formaliser tide, scoped partial.** New file `lean/DLNFibre/Core/FibreBundleTransition.lean`, wired by
the controller; whole library green (3786 jobs); all 8 headlines axiom-clean `[propext, Classical.choice,
Quot.sound]` (controller-gated). Reviewer PASS WITH CONCERNS (the one concern actioned). **Honestly NOT
named `locallyTrivial`** — the cocycle lives on the ambient cover, not yet on the Schur chart.

## What is EARNED — the genuine ring-level transition cocycle (NOT existential GL×GL transport)
- `awayOverlapTransition (f g : R) : awayOverlap f g ≃ₐ[R] awayOverlap g f` — the transition `AlgEquiv`
  on `D(f) ∩ D(g)`. Both `awayOverlap f g := Away (algebraMap R (Away f) g)` and `awayOverlap g f` are
  genuinely `IsLocalization.Away (f*g) R` (distinct Away-of-Away towers, NOT a disguised `refl` —
  reviewer + Codex both confirmed), so this is `IsLocalization.algEquiv` between them.
- Coherence laws: `awayOverlapTransition_commutes` (fixes `R`), `_symm` (`(·).symm = swap`), `_trans_symm`
  (round-trip = id), `awayTriple_cocycle` (triple overlap `g_fg ∘ g_gh ∘ g_hf = 1`). All by localization
  initiality (`IsLocalization.algHom_subsingleton`).
- `isLocalization_awayTriple` — the triple-overlap monoid-realignment helper (`Away.of_associated`).
- Cover instantiation: `detMinorPoly s t := ((mvPolynomialX (Fin p)(Fin q) k).submatrix s t).det`;
  `eval_detMinorPoly` (eval recovers `(M.submatrix s t).det`, ties `RankMinorCover.minorChart` to
  `D(detMinorPoly s t)`); `minorChartTransition` (the per-minor overlap transition).
- The abstract `awayOverlap*` / `awayTriple*` engine is **network-free** (spin-out candidate).

## What is DISCLAIMED — the genuine remaining wall (Codex/thread-18 were right)
This cocycle is on the AMBIENT `O(Mat) = MvPolynomial` cover. It is NOT connected to the deep Schur-chart
`e_β = chartLocalizedAlgEquiv` (`Away chartDsig ≃ₐ Away chartGfib`), which exists only at the top-left
pivot of one `(d,r)`. Connecting them needs a per-pivot transport identifying each `e_{s,t}` with the
ambient presentation, OR re-deriving the ~250-LoC chart per pivot — **a separate multi-module build**
(tracked as task #118). Until then the bundle is NOT `locallyTrivial`. Card 5 of the statement card
states this precisely.

## Net B3 state (controller synthesis)
single-chart triviality (#11) + per-minor open cover + chart family (#18) + the EARNED base-space
transition cocycle (#19). **The one remaining gap to `locallyTrivial` is exactly the `e_β` ↔ ambient
bridge** (#118): identify each per-minor Schur chart `e_{s,t}` with the ambient principal-open
presentation, so the ambient cocycle transports to the chart trivializations.

## Artifacts (committed @ da137da5)
`threads/19-bundle-transition/statement-card.md` + codex consult. Lean: `Core/FibreBundleTransition.lean`.
Did NOT touch `DLNFibre.lean` or the parallel `smooth-factC` files.
