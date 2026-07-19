# Cert — Q1b: single-ψ per-node gauge fidelity (the C′/P/Q composite)

*Seat: `pen-and-paper` (pnp08), architect's Q1b (now load-bearing — coverage-t07's T3 real-atlas
chart-slot filling consumes the ψ shape). Exact `sympy`; formulae pinned to Aoyagi pp.16–21 (corner
normalize, `Q` p.17, `P` p.18, `C'=Q^{-1}C`, `D'''=[1 O; O D_{J+1}]`). Battery `battery/single-psi.py`
(exit-0). Decorrelated Codex leg (`codex/single-psi-{prompt,answer}.md`, hypothesis withheld) — converged.
Refines cert-shear-gauge.md (which established `chartMap=ψ∘β`, ψ≠id).*

## Question

Does ONE variable-dependent shear `ψ` per node faithfully factor the paper's `C'/P/Q` composite, or is a
COMPOSITION required (the coverage lane's chart-slot shape)?

## VERDICT: single-ψ is FAITHFUL as ONE unipotent map — but it is NOT a single *elementary* shear.

**What the composite actually is (two-way, exact).** `[CERT]` At a pivot-clearing node (case-1(2) / case-2)
the paper factors the corner via the blow-up `β`, then RIGHT-multiplies the residual by the upper-unipotent
`Q` (clears row 1) and LEFT-multiplies by the lower-unipotent `P` (clears col 1), and relabels
`C'=Q^{-1}C`. The **faithful combined action is TWO-SIDED**: `D ↦ P·D·Q` (on `vec(D)` it is `Q^T ⊗ P`),
together with `C ↦ Q^{-1}C`. Its net effect on coordinates is the **single Schur-complement gauge**
> `d_{ij} ↦ d_{ij} − d_{i1} d_{1j}` (residual interior), ratios fixed; `c_1 ↦ c_1 + Σ_j d_{1j} c_j` (row-mix),
verified exactly at 2×2, 3×3, 4×4: `D''' = [1 O; O (D − col₁·row₁)]`, **Jacobian det = 1, unit-triangular,
all eigenvalues 1 — one UNIPOTENT map**. `Q`, `P` are merely the *algorithm* that computes this one gauge.

**The load-bearing distinction (Codex sharpening, battery-confirmed).** `[CERT]` The displacement
`rank(J_ψ − I) = 2, 4, 6, …` (grows with block size) — so ψ is **NOT a single elementary (rank-1)
transvection**, even though it is one unit-triangular unipotent map. (Two independent pieces already at
2×2: the residual Schur update AND the `C` row-mix.) The classification is **(b) one unipotent map, not
(a) one elementary shear**.

**A trap ruled out.** `[CERT]` The *same-side* product `P·Q` (upper·lower) is **non-unipotent**
(`χ = λ²−(2+ρxy)λ+1`, eigenvalues ≠ 1) — but that is NOT the faithful action; the gauge is the two-sided
`P·D·Q` (`Q^T⊗P`, unipotent). Do not model the node gauge as `(P·Q)·D`.

## Chart-slot verdict for the coverage lane

`[CERT]` **Single-ψ is FAITHFUL provided the chart-slot holds ONE general variable-dependent
unipotent/unimodular map** — exactly the compass region-glue ψ shape ("a bounded-unit local diffeo with
full inverse data", `|det Dψ| = 1` here). Under that shape, one ψ per node suffices — NO composition
needed. **It is INFIDELITOUS only if the slot restricts ψ to a single elementary shear (rank-1
transvection)**; then the node needs the ordered column-then-row composition `ψ = ψ_Q ; ψ_P` (or the
explicit Schur gauge, which is one map of displacement-rank ≥ 2).

So: **not an emergency flag** — the intended ψ shape (general bounded-unit diffeo) is faithful with one ψ
per node. The single design constraint to respect: **do not encode the per-node ψ as one elementary
shear**; encode it as the Schur-complement gauge (one unipotent map, det 1, rank-≥2 displacement) or the
`Q`-then-`P` ordered pair. The leaf `chartMap` is the fold of these per-node single gauges; case-1(1)
merges carry no gauge (`ψ = id`, only the exponent/tail update).

## Codex decorrelation

`[OBS]` Codex independently: computed `D''`, `P`, the two-sided `Q^T⊗P` (unit-triangular, det 1, eigenvalues
1) and the `C` relabel; flagged that `P·Q` (same-side) is the non-faithful non-unipotent product; and
concluded classification **(b)** — one unipotent map, not one elementary shear (`rank(J_ψ−I) ≥ 2`), so a
single-elementary-shear slot needs the `Q`-then-`P` composition. `[OBS]` Codex "most likely wrong": guarding
against three misreadings — "triangular Jacobian ⟹ one elementary shear" (false), "non-unipotent because
`PQ` is" (false; wrong product), "one slot can't hold it" (false; one function suffices). All three align
with my exact computation.

## Close

- **Firmest:** the per-node gauge is ONE unipotent map (the Schur-complement gauge, det 1) — single-ψ
  faithful under the general-diffeo ψ shape; NOT a single elementary shear (displacement rank ≥ 2).
  Two-way, exact (2×2/3×3/4×4).
- **The one caveat for the coverage lane:** encode ψ as a general unipotent gauge (or `Q`-then-`P`), never
  as a single elementary transvection. No composition is needed beyond that; the `chartMap` fold over
  nodes is unchanged.
