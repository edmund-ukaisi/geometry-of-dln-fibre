# R1 re-scope — corrected resolution_charts (CORE) + product_reduction wiring

- **Seat:** `pp` (leading R1). Task #47. The 14th-finding re-scope (APPROVED @c42a1a3) made concrete:
  the exact corrected `resolution_charts` statement + the `product_reduction` wiring chain.

## The corrected `resolution_charts` (CORE form)

The current statement `rlctAt H (dlnLoss H B) wstar = ⨅ monomialThreshold` is FALSE for r>0 (min vs
sum). Re-scope to the CORE `‖∏C‖²` (= `dlnLoss M 0` on reduced widths `M`, at the origin):

```
theorem resolution_charts (M : Fin (L + 1) → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAt M (dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ)) (0 : Params M)
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i)
```
- `B = 0` (the singular core, product 0 at origin); `wstar = 0` (the deepest core point).
- `M` is the reduced widths (the caller passes `M = fun s => H s − r`).
- Drops the spurious general `(B, wstar)` — R1 is about the core at its origin, full stop.
- **KEEP `rlctAt` (NOT `rlctAtOn`)** — FINAL FORM, delivered to fm 2026-06-21. Aligns with the existing
  `resolution_charts_case111` (which already proves `rlctAt (![1,1,1]) (dlnLoss (![1,1,1]) 0) deepest111`,
  `deepest111 = fun _ => 0 = (0 : Params)`) AND the `product_reduction` wiring (both use `rlctAt`). So
  case111 becomes the M=(1,1,1) instance with the SAME witness/proof — near-defeq realign. (`rlctAtOn`
  would equal it via `rlctAtOn_eq_rlctAt`, but `rlctAt` minimises fm's churn. No downstream caller of
  `resolution_charts` exists — collision-free swap.)

This is the VALUE-MATCH (R1's deliverable): the resolution's chart family `(ι,d,k,h)` reconstructs
the core RLCT. It is NOT a chart↔Adm bijection (charts outnumber strata — STALE docstring; fix it).

## The value `⨅ monomialThreshold = lambdaCore` is A1's job (separate)

Keep R1 = the chart fact (`rlctAtOn(core 0)0 = ⨅ monomialThreshold`). A1 separately proves
`⨅ monomialThreshold = ofReal(lambdaCore M)` via:
- S2 `monomial_rlct`: `monomialThreshold d k h = ⨅_j axisRatio (h j)(k j)`;
- `lambdaCore_eq_clean` + the chart (k,h) data: `⨅ over charts ⨅_j axisRatio = ½·min Mval = lambdaCore`.
This separation keeps R1 (geometry/charts) and A1 (arithmetic) clean.

## The `product_reduction` wiring (the approved re-scope)

```
rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
  = [block_elimination (L1): B → diag(E_r,0), regular P,Q; S1.3 rlct_unit_invariant / ideal-inv]
    rlctAt of the split loss (reg-block Σx² ⊞ core ‖∏C‖²)
  = [S1Fubini (n=1 iterated ×n): adds n/2, n = r(H¹+H^{L+1})−r²]
    (n/2 : ℝ≥0∞) + rlctAtOn (dlnLoss M 0) (0 : Params M)          [M = fun s => H s − r]
  = [resolution_charts (core) + S2 monomial_rlct + A1 lambdaCore_eq_clean]
    (n/2) + ofReal(lambdaCore M)
  = ofReal( [−r²+r(H¹+H^{L+1})]/2 + lambdaCore M )                 [n/2 = the reg term, VERIFIED]
  = ofReal(aoyagiLambda H r).                                       [Lambda def]
```
VERIFIED: `n/2 = [−r²+r(H¹+H^{L+1})]/2` exactly (`/tmp/r1_rescope_stmt.py`, all cases). So
`aoyagiLambda = n/2 + lambdaCore` and the chain closes.

## The Fubini split obligation (the one wiring subtlety)

The step `dlnLoss(deepest) = reg-block ⊞ core` (disjoint variable blocks) is the L2/block-elim
content: at the deepest point, in the split coordinates, the error matrix is
`[[C₁−E_r, F₂],[F₃, ∏C − F₃F₂]]` (Skeleton p.13 structure); the regular generators `{C₁−E_r,F₂,F₃}`
(n of them, the Σx² block) and the core `∏C` are in disjoint variables (S1.3 drops the F₃F₂ cross
term as it's in the regular ideal). Then S1Fubini applies (`rlctAt(Σx²+core) = n/2 + rlctAt(core)`).
The unit-absorption obligation (chart core = unit·monomial) is inside resolution_charts/A1's S2 use.

## NET — hand fm

1. **Re-scope `resolution_charts` to the CORE form above** (B=0, origin, reduced widths M).
2. **Fix the stale docstring** (drop "exponents range over exactly Adm" → "the value-match: the chart
   family reconstructs rlctAtOn(core); the chart exponents realise ½·min Mval; NOT a chart↔Adm
   bijection (charts outnumber strata)").
3. **product_reduction wiring chain** as above (block_elim → S1Fubini → resolution_charts-core + S2 +
   A1). The n/2 = reg-term identity is verified.
This is the architecture the 14th-finding re-scope approves, made into exact targets.
