# threads.md — `rlct-payoff` thread index

Status ∈ `open` / `in-progress` / `blocked` / `review-pending` / `closed` / `abandoned`.
Each thread's artefacts live under `threads/<NN>-<slug>/`.

| # | slug | type | status | one-line outcome |
|---|------|------|--------|------------------|
| 01 | sizing-mathlib-coverage | scout | closed | Mathlib coverage: irreducibleComponents / variety-of-union / SLT-RLCT machinery |
| 02 | sizing-math-stratification | pen-and-paper | closed | Σ^r = ⋃ Ō_M stratification + components=maximal-orbits + (C/2,θ) assembly statement |

| 03 | G-stratification | formaliser | closed | G1 link (mult=submult corner) + set-level Gabriel membership + G2 `Σ̄^r = ⋃ Ō_M` |

| 04 | G3-components | formaliser | closed | irreducible components of Σ̄^r = maximal Ō_M; top-dim = min-codim → θ=numTop (spec-transport spike first) |

| 05 | theta-count | formaliser | closed | numTop = θ = #top-dim components (Kostant↔component count-bijection) |

| 06 | theta-discharge | formaliser | closed | Brick2 Gabriel recovery LANDED; Brick1 reduced to cCodim·0 dim-monotonicity |
| 07 | ccodim-zero-mono | formaliser | review-pending | cCodim e 0 ≤/< cCodim e' 0 (shortest-interval-split delta-sign) ⟹ θ=numTop unconditional |

| 08 | ccodim-zero-strict | formaliser | open | cCodim e 0 < cCodim e' 0 (all-vertex) via +1-step invariant ⟹ θ=numTop UNCONDITIONAL |

Threads open dynamically as the sizing recon re-scopes the ladder (Phase G/θ/D/R builds).
