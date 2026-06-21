# Route B certificate — `cCodim_zero_strict` (strict-cert peer, decorrelated)

Source: the `strict-cert` pen-and-paper peer (decorrelated: its own exhaustive enumeration + an
independent Codex derivation CONVERGED). **Status: certificate (pen-and-paper + exact-integer numerics),
NOT yet Lean.** The same seat RETRACTED an earlier ("flat-chain") route — so BUILD CAREFULLY, verify each
lemma compiles against the real defs, do NOT assume; if a sub-step fails to hold, report (no sorry-patch).
Est. ~50–70 LoC on top of the LANDED weak monotonicity.

## Target
`cCodim_zero_strict` (all-vertex strict): `(∀ v, e v < e' v) → cCodim e 0 < cCodim e' 0`. Discharging it
discharges `hMonoStrict` ⟹ `Core.CCodimCornerMono.numTop_eq_ncard_topComponents_of_strict` becomes
UNCONDITIONAL (`θ = #top-dimensional irreducible components of Σ̄^r`).

## Reuses the EXISTING machinery (no new move, no Φ functional)
`Core.CCodimZeroMono`: `reduceStep` + the four atomic moves `redMove`/`leftShrink`/`rightShrink`/`removeMove`,
their `codimForm_*_le` ("delta ≤ 0") sign lemmas, `splitDelta`/`rrInd`/`llInd`/`splitCoeff_pos_imp`, and the
LANDED `cCodim_zero_mono` (weak). `codimForm` pairing: `pair(A=[a,b], B=[c,d]) ⟺ a<c≤b+1 ∧ b<d` (the Ext form).

## Lemma Y — full coverage ⟹ `codimForm ≥ 1`
If `e v ≥ 1` at every vertex `v`, then EVERY corner-0 Kostant partition `m` of `e` has `codimForm(extendℤ m) ≥ 1`.
Proof (contrapositive): if `codimForm = 0` the active intervals are pairwise non-pairing. Vertex 0 is covered ⟹
some `[0,b]` active; take `b` maximal; corner-0 ⟹ `b<N`. Pair-free ⟹ nothing pairs `[0,b]`, i.e. no active
`[c,d]` with `0<c≤b+1, b<d`. Vertex `b+1` (exists, `b<N`) needs a covering `[c,d]` with `c≤b+1≤d, b<d`;
pair-free forces `c=0`, i.e. `[0,d]` with `d>b` — contradicting `b` maximal. So `b+1` is uncovered,
contradicting full coverage. (Verified N≤4: 3305/3305 full-coverage partitions have codimForm ≥ 1, min = 1.)

## Lemma X (the crux / new content) — `codimForm ≥ 1` ⟹ a STRICT `reduceStep` exists
If `codimForm(extendℤ m) ≥ 1` then some covered vertex `k` has a SHORTEST-covering `reduceStep` (the existing
`redMove`/`leftShrink`/`rightShrink`/`removeMove` at `k`) that is STRICT (`delta < 0`).
Extremal construction (verified 379877/379877; needs only `codimForm ≥ 1`):
- `codimForm ≥ 1` ⟹ some active interval is involved in a pair. Pick `I` = a **minimal-LENGTH** active interval
  involved in a pair (length `ℓ([u,v]) := v−u`; finiteness gives the min).
- **Case 1** `I = A = [a,b]` is the LEFT of a pair `A→B = [c,d]` (`a<c≤b+1, b<d`): reduce `A` at `p = c−1 ∈ [a,b]`.
  - `A` is SHORTEST active covering `p`: else a shorter active `C=[x,y]∋p`; if `y<d` then `C→B`, if `y≥d` then
    `A→C` (using `ℓ(C)<ℓ(A)`) — either way `C` is pair-involved & shorter, contradiction.
  - The move (interior split / `leftShrink` if `p=a` / `rightShrink` if `p=b` / `removeMove` if singleton) has
    the partner `B` at coefficient EXACTLY `−1`, and "shortest" kills all positive coeffs (the existing sign
    lemma `splitCoeff_pos_imp`) ⟹ `delta = ∑_Y m(Y)·coeff(Y) ≤ −m(B) ≤ −1 < 0`.
- **Case 2** `I = B = [c,d]` is the RIGHT of a pair `A→B`: symmetric, reduce `B` at `q = b+1 ∈ [c,d]`; `B` shortest
  covering `q` (mirror contradiction); partner `A` at coeff `−1`; `delta ≤ −m(A) ≤ −1 < 0`.
- `coeff(partner) = −1` confirmed exactly in all four move types (Cases 1 & 2). Lemma X just upgrades the
  existing `codimForm_*_le` ("≤0") to "<0" by noting a PRESENT partner (`m(B)≥1`) sits on a `−1` coefficient.

## The +1 step ⟹ all-vertex strict (the wiring; verified end-to-end 252/252)
- `cCodim e 0 < cCodim (e+1) 0` for full-coverage `e+1`: take a minimiser `m₊` of `e+1`;
  `codimForm(m₊) = cCodim(e+1) ≥ 1` (Lemma Y). Lemma X ⟹ a strict `reduceStep` at some `k` ⟹ `m″ ∈
  kostantPartitions (update (e+1) k ((e+1)k − 1)) 0` with `codimForm(m″) ≤ cCodim(e+1) − 1`. The decremented
  vector = `e + (1 everywhere except k) ≥ e`; LANDED weak-mono ⟹ `cCodim e 0 ≤ codimForm(m″) ≤ cCodim(e+1)0 − 1`.
- `cCodim_zero_strict`: set `f := e+1` (pointwise); `e ≤ f ≤ e'`, `f` full-coverage; `cCodim e 0 < cCodim f 0`
  (+1 step) `≤ cCodim e' 0` (weak mono). Done.

## RULED OUT (don't re-explore)
- Route A (simple/linear Φ with `codimForm ≥ Φ ≥ cCodim(e)+1`): FAILS — the +1 gap is often exactly 1 (tight),
  no simple Φ carries it (Φ_adjacent fails 191/800).
- Every DETERMINISTIC LOCAL step-selection rule tried FAILS (globally-shortest; longest; minimal-pair endpoints;
  shortest covering vertex 0; smallest right-endpoint) — the strict step's LOCATION is config-dependent. The
  load-bearing refinement is "involved-in-a-pair + extremal-by-length" (Lemma X).

## MOST LIKELY TO BREAK (the one non-mechanical Lean step)
The "shortest-covering" contradiction inside Lemma X (Case 1/2): that `A` (resp `B`) is shortest active covering
`p=c−1` (resp `q=b+1`), using `ℓ(C)<ℓ(A)` twice with a `y<d` vs `y≥d` interval-arithmetic case split.
Elementary (`Fin`/`omega`) but the only non-mechanical part — pin its exact obligations first.

## Reserve route (cleaner but NEEDS A NEW MOVE — prefer Route B)
"Corner-uncross": in a minimiser of `e+1` every pair is forced to be a CORNER pair `([0,b],[c,N])` (else the
coverage-preserving uncross `[a,b]+[c,d]→[a,d]+[c,b]`, valid when `(a,d)≠(0,N)`, strictly drops codimForm,
contradicting minimality; verified 256521/256521). Then `[0,b]+[c,N] → [c,b]` decrements coverage by 1 at EVERY
vertex (→ partition of `e`), keeps corner-0, strict. Needs a new move + delta lemma — Route B reuses existing.
