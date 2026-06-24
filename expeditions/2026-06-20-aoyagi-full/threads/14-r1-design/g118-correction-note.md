# G3.2 architecture — (A) det-1 vs (B) blow-up: CORRECTED CONTRACT (pp-hall, 2026-06-21, task #118)

**fm-2 stop-before-lines catch.** The general-M recursion: is the chart (A) det-1 / measure-preserving
(clean `nReg/2` chain) OR (B) a blow-up with nontrivial Jacobian (`⨅ monomialThreshold` like (2,2,2)) OR
both? This may be a gap in the #109 GATE GO (it was — see the honest revision below).

**Verdict: BOTH-IN-SEQUENCE per recursion node.** Two decorrelated legs converged (pp-hall exact + Codex
xhigh). (A) alone is FALSE for the zero-core resolution; (B) alone is incomplete without the Schur
normalization. My #109 cert's "det-1 clean, bottoms at smooth leaf" framing was IMPRECISE for the
zero-core and is corrected here.

## The two recursions were conflated — disentangled
There are TWO distinct recursions, and #109's cert blurred them:

**RECURSION 1 — the B≠0 rank-r PRODUCT REDUCTION (Aoyagi Thm 3 / `product_reduction` / L2):**
`F = ‖∏C − B‖²`, `B` rank `r > 0`. A det-1 UNIMODULAR `Q^(s)` Schur-peel (the `(u_i,ψ_i)` adapted
basis, Jacobian **= 1**, measure-preserving) splits `F = ‖reg E_r‖² + ‖∏C'‖²`, `C'` the reduced chain,
`B' = 0`. This peels the `r` REGULAR generators — the `nReg/2 = [−r²+r(H¹+H^{L+1})]/2` SHIFT, additive
via S1.5 Fubini. **REQUIRES a leading minor to be a UNIT** (the `B≠0` regular block provides it).
**This is what #109's symbolic algebra (all diff=0) validated — and it is CORRECT.** It TERMINATES at
the residual zero-core `‖∏C'‖²` (B'=0) — which is STILL SINGULAR, NOT a smooth leaf.

**RECURSION 2 — the ZERO-CORE RESOLUTION (R1 / #111 / the (2,2,2) ladder):**
resolve `‖∏C'‖²` at the ORIGIN (`B'=0`). At the origin `P[0,0]=0` is NOT a unit, so the det-1 Schur
chart HYPOTHESIS FAILS — you cannot peel cleanly. You must **BLOW UP** first.

## The general-M recursion node (the corrected Lean contract for fm-2)
Each node of the ZERO-CORE resolution = **(B) blow-up THEN (A) det-1 Schur**, interleaved:

1. **(B) Blow up** the rank-stratum center `S(t)`, codim `c = Mval(t)`. Affine chart `y_a = u`,
   `y_j = u·v_j` (`j≠a`, the `c` center-coords), spectators `z`. **Jacobian `= |u|^{c-1} = |u|^{Mval(t)-1}`**.
   Pullback `F∘π = u²·F_res`. ⟹ exceptional divisor `(k,h) = (1, Mval(t)−1)`, ratio `(h+1)/(2k) =
   Mval(t)/2`. **THIS is the monomial weight** (feeds `monomialThreshold`, #113's `g5_pivotNode`).
2. **(A) det-1 Schur** within the chart: now `Ahat`'s pivot (e.g. `Ahat[0,0]=1`) is a UNIT, so the
   Lemma-2 / `(u_i,ψ_i)` unimodular clear applies. **Jacobian = 1 (unit)**, no weight. It reduces
   `F_res` to a smaller-chain zero-core `‖∏C'‖²` (the strict-transform / Schur reduction — the SAME
   substitution #109 validated, all diff=0).
3. **Recurse** on the residual zero-core `‖∏C'‖²`.

**The monomial weights come from the (B) blow-up Jacobians; the (A) det-1 Schur is the unit-Jacobian
chain-reduction WITHIN each chart (contributes NO weight).**

## Terminal leaf (fm-2's base-case question)
The zero-core resolution's terminal leaf is **monomial × (unit | residual smooth block)**, NOT a smooth
single-matrix L=1 block:
- `F∘π = unit · ∏ᵢ|uᵢ|^{2kᵢ}` (pure monomial leaf), OR
- `F∘π = unit · ∏ᵢ|uᵢ|^{2kᵢ} · (z₁²+…+z_d²)` (monomial × residual smooth block).
- The all-dims-1 leaf is the pure monomial `(c₁···c_L)²` (rlct 1/2 for all L), NOT a smooth block.
- (2,2,2): 8 pure-monomial unit-leaves + 16 monomial × smooth-4-block leaves. Headline `⨅ = 3/2`.
fm-2's L=1 smooth single-matrix base (`dlnLoss_one_layer_deepest`) is the base of the **(A) chain
reduction WITHIN a chart** (the det-1 product-reduction's leaf), **NOT** the terminal leaf of the **(B)
resolution** — they are different recursions. Do not conflate them in the base case.

## Headline + reconciliation with (2,2,2) / #113
- Zero-core headline = `⨅_leaves monomialThreshold(d,k,h)` (B-flavored), with divisor ratios
  `(hᵢ+1)/(2kᵢ)`. The det-1 Schur appears only as the measure-preserving chain-reduction inside each
  blow-up chart. So the general-M recursion FEEDS `g5_pivotNode` / `monomialThreshold` (#113's cover),
  consistent with the (2,2,2) ladder's blow-up architecture.
- Full assembly: `rlctAt(‖∏C−B‖²) = nReg/2 [Recursion-1, det-1 Thm-3 product reduction, B≠0 regular peel]
  + lambdaCore [Recursion-2, the blow-up resolution of the B'=0 zero-core, ⨅ monomialThreshold = ½·min_Adm
  Mval]`. Both terms appear in `aoyagiLambda`. They are SEPARATE rungs.

## The honest revision to #109's GATE GO
- **What #109 correctly validated (STILL SOUND):** the Schur SUBSTITUTION `D_i = Q^(i-1) C^(i) (Q^(i))^{-1}
  = blockdiag[λ_i, C'_i]`, `Schur(P) = ∏C'_i`, all diff=0, threading for all L. This IS the (A) det-1
  chain-reduction step.
- **What was IMPRECISE (now corrected):** "the recursion bottoms out at a smooth block leaf" + the
  reading that det-1 Q ALONE closes the resolution. For the ZERO-CORE resolution that is WRONG — the
  resolution NEEDS the (B) blow-up at each node (the det-1 chart hypothesis fails at the singular origin),
  and the headline is `⨅ monomialThreshold`, not a clean `nReg/2` chain, with monomial (not smooth) leaves.
- **Net:** the general-R1 route is still construction-not-open-math, but the recursion NODE is the
  **(B)-blow-up + (A)-Schur composite**, and fm-2's `IsSchurChart` contract must carry **a Jacobian-weight
  field** (`(k,h)` per exceptional from the blow-up), NOT a pure measure-preserving field. The det-1
  Schur is a unit-Jacobian SUB-step of the node, not the node itself. **fm-2's stop was correct; #109's
  GATE GO is amended to "GO with the (B)+(A) composite node contract", not the (A)-clean contract.**

Decorrelation: pp-hall exact (5 scripts `g118-scripts/`: two-recursions disentangle, det-1-fails-at-origin,
the (B)-then-(A) interleave, the explicit `|u|^{Mval-1}` node Jacobian, the terminal-leaf type) + Codex
xhigh (independent: BOTH-IN-SEQUENCE, same Jacobian, same terminal leaf, blunt "the earlier smooth-leaf
framing was imprecise/wrong for the zero-core"). Converged. Consult `codex/g118-A-vs-B-{prompt,answer}.md`.
