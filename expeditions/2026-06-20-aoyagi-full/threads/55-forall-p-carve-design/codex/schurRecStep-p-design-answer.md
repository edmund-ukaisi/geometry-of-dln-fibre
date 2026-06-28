1. **VERDICT**

Option B is the right Lean object. Reusing `minAdm (![r,r,p]) / 2` keeps the Schur threshold aligned with the global Aoyagi/minAdm library and avoids a later bridge theorem from a fresh one-variable min.

Biggest risk: [MED] `minAdm` is not definitionally the one-variable range-min; locally it is `Adm.inf' ... Mval` with `minAdmRec_eq_minAdm` as the bridge. So expect dependent `Fin 3`, `![r,r,p]`, `redChain`, and `inf'` friction. I am inferring the exact Mathlib lemma names here; verify the `Finset.inf'` attained-min API in v4.29.

Recommendation: go with Option B, but first land a tiny API:
`minAdm_rrp_eq_range`, `schurLambdaP_zero/one`, and `minAdm_rrp_subadd`. Downstream proofs should not unfold raw `minAdm`.

2. **peel_le**

Sound and Lean-tractable, but not quite “one `inf'_le_of_le`” unless the residual minimizer is already in hand. You need either an attained-min witness for the residual `inf'` or a local lemma that packages it.

The proof shape is fine: choose residual minimizer `t' ≤ r-j`, lift to `t'+j ≤ r`, apply `inf'_le` on the big range, then use
`r - (t' + j) = r - j - t'`
before the semiring identity. Hidden case `j = r` is benign: residual is `0`, `t'=0`, candidate is `r`. Risk [LOW], with [MED] only for exact `inf'` API/name friction.

3. **r=2**

Use a separate p-general `r=2` base. Do not loosen `hr : 3 ≤ r`.

Reason: the current firing is structurally built for `r≥3` and, more importantly, for a p=4 numerical slack pattern: peel threshold `2`, fallback exponent `3`, and `3 < schurLambda r`. At `r=2`, p=4 already has no room for the mid peel (`c' > 2` while `c' < 2`), so loosening indices cannot recover the proof. A p-lift of `core_schur2` is cleaner and isolates the special low-corank geometry.

4. **CONFOUND**

[HIGH] The main non-mechanical part is not the angular `r²-1` carve; it is the exponent routing inside the firing engine. The p=4 proof silently relies on the fixed split
`c' > 2` peel with residual `c'' = c' - 2`, and subcritical reduction to exponent `3`. For general p this must become a p-dependent split around `p/2`.

In cap-B regimes, `lam r ≤ p/2` can happen, so there may be no peel range at all; those cases should close by the uniform Morse bound for `c' < p/2`, not by recursion. When `p/2 < lam r`, choose a flexible `c★` with `max c' (p/2) < c★ < lam r` for the reduction, then peel at exponent `c★`. The existing fixed `3` pattern will bite first.

Also handle `p=0` explicitly if the theorem is truly `∀ p : ℕ`: thresholds are vacuous, but analytic lemmas over `Fin p` should not be invoked.

5. **Go / No-Go**

Go, with one required design change before diff-gating: add the p-dependent ratio-residual split API (`c' < p/2` direct Morse; `p/2 < c'` peel/IH; equality handled by choosing `c★`) before doing the large `Fin 4 → Fin p` width swap.