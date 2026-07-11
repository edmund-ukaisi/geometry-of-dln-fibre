# Soundness check — `qPeelIntegral_lt_top` STATEMENT (route-S gate) — VERDICT: PASS

**Seat:** pen-and-paper (soundness audit — the route-S gate the controller reserved). **Date:** 2026-07-11.
**NO Lean build** (genm-sj5-schur building the fill in-place; scratch-read only). **Target:**
`qPeelIntegral_lt_top` (+ `qCornerSliceAtUnits`, `qCornerSliceAtUnits_le`, `qPeelIntegral`) in
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankQ.lean` (untracked). **Check:** does the STATEMENT
faithfully encode the #131 soundness (dodge the RLCT-collapse), with no hidden a.e.-deletion / weight-drop
/ min-collapse?

**Exact algebra (mine):** `/tmp/prodD/qpeel.py` (the min-cut-weight balance; gate load-bearingness).
**Decorrelated:** own `local-codex-consult` (xhigh, told to HUNT the masked collapse, PASS withheld):
`codex/qpeel-{prompt,answer}.md`. Codex returned PASS on all four + derived the joint threshold
`½·Σ min(h_i+1, m_i+1)`, confirming the gate. Adopted.

---

## VERDICT: PASS — the statement soundly encodes #131. genm-sj5-schur may build the fill. Two UPSTREAM obligations (the caller's, not statement defects) flagged.

The statement `qPeelIntegral_lt_top` is a faithful ABSTRACT encoding of the corank-q coupled majorant with
the no-collapse soundness. All three #131 requirements hold in the statement's shape, and there is no
hidden a.e.-deletion / weight-drop / min-collapse.

### (a) ADDITIVE loss, ADD threshold — PASS

`qCornerSliceAtUnits` (`:52`) is literally `∫_{[0,1]^q}(Σ_i u_i²·U_i)^{−c'}·∏_i|u_i|^{h_i}` — the loss is
the **block-additive SUM** `Σ_i u_i²·U_i`, NOT a shared-divisor / multiplicative `radialAttach`. Polar
scaling: `L(u) ≍ Σ_i u_i²` (units bounded), `∫_0^ε r^{Σ(h_i+1)−1−2c'}dr`, so the exact slice threshold is
`c' < ½·Σ(h_i+1)` — the **ADD**, not the min. The statement's hypothesis `c' < (Σ(h_i+1))/2` is exactly
this (`½·Σ(h_i+1) = 7/2` for `(3,3,3,4)` `h=![3,2]`, `= ½·minAdm` by `qPeel_threshold_eq_half_minAdm_334`).
The min `min_i(h_i+1)/2 = 3/2` would arise ONLY from the multiplicative form — which this integrand is not.

### (b) `{U_i=0}` integrated JOINTLY; the gate `h_i ≤ m_i` is the transverse charge — PASS, gate exactly right

`qPeelIntegral` (`:171`) casts `U_i = ‖X_i‖² = Σ_j (X_i)_j²` over FREE deep blocks `X_i ∈ [−T,T]^{m_i+1}`
and integrates JOINTLY over `∏_i morseBox(m_i+1) T` — the `{U_i=0}={X_i=0}` locus is IN the domain, NOT
deleted. The weighted-AM-GM decoupling (`qCornerSliceAtUnits_le`, PROVEN) at the min-cut weights
`w_i = (h_i+1)/S` (`S=Σ(h_j+1)`) gives, for `c' < S/2`:
> `2w_i c' = 2(h_i+1)c'/S < h_i+1` — u-monomial `∫∏|u_i|^{h_i−2w_ic'}` finite (`h_i−2w_ic' > −1`); and
> `2w_i c' < h_i+1 ≤ m_i+1` (by `h_i≤m_i`) — deep-Morse `∫_{[−T,T]^{m_i+1}}‖X_i‖^{−2w_ic'}` finite.

Both bind at `c'=S/2` together. **The gate `h_i≤m_i` is EXACTLY the transverse-charge condition** (Codex,
confirmed): the exact JOINT threshold is `½·Σ_i min(h_i+1, m_i+1)`, which `= ½·Σ(h_i+1) = S/2` iff every
`h_i ≤ m_i`; **any violation `h_i > m_i` gives a genuine divergence strictly below `S/2`** (the deep block
`i` diverges once `2w_i c' ≥ m_i+1`, i.e. `c' ≥ S(m_i+1)/(2(h_i+1)) < S/2`). Verified `/tmp/prodD/qpeel.py`:
tight `m=h=![3,2]` → both finite for `c'<3.5`; violated `m=![2,2]` (`h_0=3>m_0=2`) → deep block 0 diverges
at `c'=3.0 < 3.5`. **So the gate is NON-vacuous, NOT too weak, and exactly `h_i≤m_i`** (non-strict OK — the
`h_i=m_i` borderline is handled by the strict `c'<S/2`). It IS the per-block transverse product-rank
charge (`d_i = m_i+1 ≥ h_i+1 = a_i`), the #127 rescue supplied per collapse direction.

### (c) No a.e.-deletion; rpow-0 harmless — PASS

The `{X_i=0}` exceptional set (needed for the AM-GM `U_i>0` hypothesis) is joint-null (each `X_i=0` is
codim `m_i+1 ≥ 1`), so applying the positive-unit lemma a.e. is sound. Crucially, `qPeelIntegral` still
integrates over the FULL Morse boxes — it drops only the exact-zero POINTS for the a.e. inequality, NOT
their neighborhoods. If the gate were violated (`2w_ic' ≥ m_i+1`), the divergence comes from every
punctured neighborhood `0<‖X_i‖<ε`, NOT the singleton `{X_i=0}` — so a null-set modification CANNOT conceal
it. The Lean `0^{−c'}=0` (rpow) convention understates the integrand on the joint-null zero-loss locus;
harmless (measure-zero; the punctured neighborhoods are fully integrated). **This is NOT the #131
collapse-hiding a.e.-deletion** — that would drop the {U_i=0} NEIGHBORHOOD (positive-measure); here the
neighborhood is integrated via the finite deep-Morse block.

---

## The two UPSTREAM obligations (the caller's — flag, not statement defects)

The statement is a sound ABSTRACT shell in `(q,h,m,X-blocks)`. Its soundness for the ACTUAL (□) rests on
the caller (the fill's "reshape into this form") supplying:

1. **The correct per-block instantiation** (Codex-flagged, decisive): the DLN chart must genuinely supply
   FREE INDEPENDENT deep blocks with (i) the loss comparable in the correct direction to
   `Σ_i u_i²‖X_i‖²`; (ii) the combined deep-data map at full product rank; (iii) a bounded-Jacobian CoV to
   Lebesgue (the onePeel334 "clean-coordinate" linear iso, generalized to `q`); (iv) **the codimension
   available PER MATCHED BLOCK `m_i+1 ≥ h_i+1`, NOT merely as an unallocated total `D_q`.** The per-block
   allocation is stronger than "`D_q ≥ Σ(h_i+1)`" and is what the weighted-AM-GM decoupling requires — the
   product-vs-free distinction (#131: `7/2` not `9/2`) lives HERE, in the `h_i` (corner charges) and the
   per-block casting, NOT in the abstract statement (which correctly demands `h_i≤m_i`). "Without that
   instantiation, one could artificially choose large `m_i` and apply a sound abstract theorem to the wrong
   geometry" (Codex). — The `(3,3,3,4)` `q=2` anchor (`h=![3,2]`, `½·Σ(h_i+1)=7/2=½·minAdm`) is the worked
   instance the fill must reproduce; the general `q` casting is onePeel334-generalized (the fill's reshape).

2. **The zero-loss locus stays joint-null** (Codex-flagged): the rpow-0 convention is harmless ONLY because
   `{Σ_i u_i²U_i = 0}` is joint-null. It would become a real defect if an UPSTREAM degeneration made the
   zero-loss locus positive-measure. For the DLN casting (full-rank deep data, generic units) this holds;
   the fill must not instantiate with an identically-vanishing block.

Neither is a defect in the STATEMENT — both are correctness conditions on the instantiation, which is the
fill's obligation (and the natural way to reshape into this form honors them).

## Scope note

The theorem is finiteness-only (`< ⊤` below `½·Σ(h_i+1)`); the matching `rlct ≤ ½·codim` upper half stays
the Cited Watanabe interface (not this statement's job). The `q=0` specialization is vacuous
(`0≤c'<0`); intended `q≥1` instances are non-vacuous (the anchor + non-vacuity example confirm).

---

## Close

- **VERDICT: PASS.** The `qPeelIntegral_lt_top` statement faithfully encodes the #131 soundness — ADDITIVE
  loss + ADD threshold `½·Σ(h_i+1)` (not min), `{U_i=0}` integrated JOINTLY over the full deep boxes (not
  a.e.-deleted), and the gate `h_i≤m_i` is EXACTLY the per-block transverse-charge condition (non-vacuous,
  not too weak; joint threshold `½·Σmin(h_i+1,m_i+1) = ½·Σ(h_i+1)` iff `h_i≤m_i`, violation → divergence
  below). No hidden weight-drop / min-collapse / positive-measure a.e.-deletion. Confirmed by my exact
  balance + a decorrelated Codex (told to hunt the collapse) — PASS on all four, joint-threshold-confirmed.
  **genm-sj5-schur may sink the ~100 LoC Tonelli fill.**
- **The two upstream obligations** (the caller's, not statement flaws): (1) the per-block casting must
  supply `m_i+1 ≥ h_i+1` PER MATCHED BLOCK (not an unallocated total `D_q`) with a bounded-Jacobian
  clean-coordinate CoV + full product rank + correct `h_i` (the `7/2`-giving corner charges) — this is
  where the product-vs-free distinction lives; (2) the zero-loss locus must stay joint-null. Both are
  honored by the natural onePeel334-generalized reshape.
- **For the FILL's proof (the route-S gate, restated):** the ~100 LoC Tonelli fill must (i) apply the
  proven `qCornerSliceAtUnits_le` at the min-cut weights `w_i=(h_i+1)/S`, (ii) `q`-fold-Tonelli-factor into
  the `q` deep-Morse blocks + the u-monomial box, (iii) discharge each deep-Morse block over the FULL box
  (capturing the `{X_i→0}` neighborhood — NOT deleting it) via the gate `2w_ic' < m_i+1`. The statement
  sets this route up correctly; the fill just executes it.
