# Thread 25 — H3 rank-count / fibre-dimension CERTIFICATE (pen-and-paper, 2026-06-24)

*(Recorded on the worktree branch by the controller from `pp-jacobian-rank`'s report; the agent's
own write landed in the main checkout, spawned agents defaulting to that cwd — see lessons (I).)*

## Headline — CERTIFIED

`dim mult⁻¹(E) = card − C − δ` (so `codimRepCanonical(fibre over E) = C + δ`), where `card = dim Rep_d
= Σ_i d_{i+1}·d_i`, `C = cCodim d r = codim Σ̄^r`, `δ = r(d_N+d_0−r)`, `E = diag(I_r,0)`. Equivalently
`rank(d mult) = C + δ` at a generic point of a **top-dimensional** component of the fibre.

Verified **two independent exact ways**:
- **Singular Krull dim** of `mult⁻¹(E)` (exact ℚ) `= card−C−δ` in ALL 13 cases: `(2,2,2)` r=0,1,2;
  `(2,2,3)` r=0,1,2; `(1,2,1)` r=0,1; `(3,3,3)` r=1,2; **`(2,2,2,2)` r=0,1,2 (N=3 chain)**. Every row matches.
- **Exact sympy Jacobian rank** at explicit generic top-component points `= C+δ`: `(2,2,2)` r=1→4, r=0→3,
  r=2→4; `(3,2,3)` r=1→7; `(3,3,3)` r=1→8; `(1,2,1)` r=0→1.

Explicit anchor generic point `(2,2,2)` r=1: `A_0=[[1,0],[0,0]]` (rk1), `A_1=[[1,2],[0,3]]` (rk2),
`A_1A_0 = E`, `rank(d mult) = 4`.

## Structural reason (clean, general) — the FIBRATION

`δ = dim Mat^{≤r}` (the rank-`≤r` locus dimension in the **target**, `= r(d_N+d_0−r)`, LANDED as the
thermometer `DeterminantalStratumDim`). The restricted multiplication `mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{≤r}`
is **dominant**; `E` is a generic (rank-exactly-`r`) point of `Mat^{≤r}`, so the **generic-fibre-dimension
theorem** gives `dim F = dim Σ̄^r − dim Mat^{≤r} = (card−C) − δ`. So **+C** = the genuine `Σ̄^r`
codimension (the engine's Kostant/Ext content, LANDED `SigmaCodim`), **+δ** = directions lost by pinning
to the exact point `E` inside its `δ`-dim rank-`r` stratum. The fibration count reproduces every Singular row.

## CRITICAL SCOPE (load-bearing for the formaliser)

`F` is **reducible**; rank is lower-semicontinuous ⟹ across components, higher rank ⟺ lower dim.
Lower-dim components carry rank UP TO `d_N·d_0` (full submersion). E.g. `(2,2,3)` r=1: top comp
`{A_0 rk1, A_1 rk2}` dim 5 rank 5, but `{A_0 rk2, A_1 rk1}` is a dim-4 comp with rank 6. `(2,2,2)` r=0:
`{A_0=0}` is dim-4 rank-4, NOT top. So **"rank = C+δ at ANY generic fibre point" is FALSE**; correct =
"at a generic point of a **TOP** component" (= the minimizing-Kostant profile). Identifying it is
dimension-dependent, NOT a uniform factor-rank recipe.

## Recommendation to the formaliser

Do **NOT** prove "rank = C+δ generically" by constructing the generic point (top component varies with
`d, r`). Instead:
1. **`dim F = card−C−δ` via the fibration** `mult|_{Σ̄^r} ↠ Mat^{≤r}` + generic-fibre-dim + `dim
   Mat^{≤r} = δ` (thermometer) + LANDED `dim Σ̄^r = card−C` (`SigmaCodim`). This IS the H4 content and
   **sidesteps per-component rank bookkeeping** (and flatness — generic flatness is free).
2. `rank = C+δ` then follows on a generically-reduced top component via `card − dim` (H3a's
   `finrank ker + rank = card`) — a corollary, not the target. Non-vacuity witness: anchor
   `rank(J A*) = 4` for `(2,2,2)` r=1 by `decide` on the explicit matrix.

## Kill-condition / hypotheses

Needs `r ≤ min_i d_i` (E realizable / the rank-`r` stratum is hit) — the dominance hypothesis
(decorrelated Codex gpt-5.5 flagged it, confirmed the fibration count, corrected a false
`image ⊆ T_E Mat^{≤r}` bound). Only **generic-reducedness of the TOP component** is needed (NOT global
reducedness — the thread-20 radicality wall stays off-path).
