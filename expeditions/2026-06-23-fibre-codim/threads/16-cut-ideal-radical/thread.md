# thread 16 — cut-ideal radical certification (R2-2/R2-3 ideal-transport, pen-and-paper)

**Type:** pen-and-paper (specialised scout) · a sharp truth-value adjudication via exact algebra. NO Lean.
R2-2 (thread 15) found verdict **L**: the G2-3 endpoint-normalization route needs an ideal-transport the
engine doesn't supply, and it hinges on a **radical/reducedness** fact that must be certified before any
formaliser builds the AlgEquiv. Hand back a certificate (the mechanism) or an obstruction (→ re-route).

## Read first
- `threads/15-total-ring-presentation/codex/{r2-2-presentation-prompt, r2-2-presentation-answer,
  r2-2-verdict-analysis}.md` — R2-2's wall write-up + Codex's reframing (routes a/b). **Your blueprint.**
- Synthesis §"G2-3 RECON VERDICT" (the endpoint-normalization route + the rung-ladder).
- `Core.DeterminantalBasePresentation` (R = `SchurLoc`), `Core.MultComorphism` (`multPoly`/`multComap`),
  `Core.SigmaCodim` (`sigmaIdeal = vanishingIdeal Σ̄^r`, radical; `minimalPrimes_sigmaIdeal_eq`).

## THE TRUTH-VALUE to adjudicate (sharp)
On the pivot chart, the route wants to identify the **cut presentation** `Scut := R[Ã]/(mult(Ã)−B_univ)`
(scheme-theoretic, degree-N cut equations) with the engine's **reduced** chart ring
`Sred := (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)[1/ΔP]` (`sigmaIdeal` = `vanishingIdeal(Σ̄^r)`,
radical). `Scut = Sred` ⟺ **the cut ideal `(mult(Ã)−B_univ)` is RADICAL** (equivalently, the fibre
`F_E = k[Ã]/(mult(Ã)−E)` is **reduced**, since the chart trivializes as a product over `R`).

**Adjudicate: is the cut ideal radical / is `F_E` reduced?** This is load-bearing: if NOT radical, the
trivialization `S ≅ R ⊗_k F_E` connects to a non-reduced object and the route (as stated) has a hole.
- **Witness (likely target):** the cut ideal IS radical / `F_E` reduced ⟹ certify the MECHANISM a
  formaliser can use (route (a) direct: `(sigmaIdeal).map(loc) = radical of the localized cut pullback`,
  or route (b) deferred: `F_E` reduced ⟹ `Scut` reduced ⟹ `Scut = Sred` post-R2-3 — say which is
  Lean-certifiable + the exact lemma chain / Mathlib handles).
- **Obstruction:** the cut ideal is NOT radical (nilpotents) ⟹ exhibit the witness + state the precise
  consequence for the route (S ≠ R⊗F_E) + the cleanest re-route (e.g. work with `Sred`/`F_E^red` directly,
  or a smoothness/Jacobian-criterion reducedness argument).

## Method (exact algebra — your remit)
- Anchor `(2,2,2), r=1`: compute a Gröbner basis of the fibre ideal `(A₂A₁ − diag(1,0))` over ℚ; test
  radical-ness (`I == radical(I)`, e.g. sympy/Singular/Macaulay2/Sage); inspect the primary decomposition
  (the recon found ≥2 components — confirm they're reduced, no embedded/nilpotent). Then a general-`N`/`d`
  argument: is the fibre `mult⁻¹(E)` (generically) reduced? (It's a "zero-product-type" locus — smooth
  locus dimension / Jacobian rank may give reducedness on the relevant component.)
- **Fire a decorrelated `local-codex-consult`** (authenticated, xhigh) on the radical-ness + the
  Lean-certifiable mechanism; save under `threads/16-cut-ideal-radical/codex/`.

## Output (certificate to controller)
A certificate hand-off for the R2-2/R2-3 formaliser: the radical/reducedness VERDICT (with the anchor
computation + the general argument), the chosen route (a vs b) + the EXACT mechanism + Mathlib/engine
handles it needs (so the formaliser builds on confirmed contracts), OR the obstruction + the re-route.
No Lean / no commits to library files. In-repo notes only; never `~/.claude/**/memory/`; don't touch
other worktrees.
