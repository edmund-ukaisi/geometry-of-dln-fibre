# Scope: is the L2 deepest-point RLCT normal form (#44) reachable via the new §SEL IFT chart?

Decorrelated reachability adjudication. Lean 4 + Mathlib, a DLN RLCT formalisation. Pure
math/architecture reasoning — I want a BOUNDED-via-chart vs RESEARCH-WALL verdict + the route. Be
adversarial and concrete.

## The target (#44, currently a NAMED sorry, ~600–1500 LoC est. via the heavy route)
`deepest_regular_core_normal_form`: at the DEEPEST point of the DLN loss (L=2, layers all rank exactly
`r`; `B = A¹A²`, rank B = r), the local RLCT is
> `rlctAt H (dlnLoss H B) (deepestPoint) = nReg/2 + lambdaCore(H − r)`
where `nReg = r(H0 + H2 − r)` and `lambdaCore(M)` is a CLOSED-FORM combinatorial value
(`½·min_T M(T)` over an admissible cone — NOT defined as an RLCT; it's the recursively-computed core).

The docstring's intended proof: a rank-`r` gauge-slice change of variables `C_s = [[I_r+X_s, Y_s],[Z_s,
T_s]]` (regular coords = output residual blocks P₁₁−I, P₁₂, P₂₁; reduced core = ‖∏C'_s‖² = dlnLoss(H−r) 0),
routed through `rlctAtOn_unit_invariant_aux` + germ-locality (the slice has unit Jacobian, NOT det ±1, so
NOT a measure-preserving change of variables). That's the heavy 600–1500 LoC obligation.

## The NEW machinery (just built, separately): the §SEL general-`v` IFT chart
For a GENERAL optimal `v` (prod v = B, rank B = r), an IFT chart Φ (selected nReg loss-minors + complement
projection, det DΦ ≠ 0 PROVEN) transfers the local RLCT:
> `rlctAt H (dlnLoss H B) v = rlctAtOn (fun (s,y) => ∑ᵢ sᵢ² + ∑ⱼ qⱼ(s,y)²) (0, t0)`
i.e. `nReg` coordinates become exact squares `∑ s²` and the rest is a C¹ residual `q`. Then a banked
quasi-split engine gives `rlctAtOn (∑s² + ∑q²) (0,t0) = nReg/2 + rlctAtOn (∑ q(0,·)²) t0` (the residual's
own RLCT). The deepest point is a SPECIAL CASE of a general optimal `v`.

## THE QUESTION
Is #44 REACHABLE by applying the §SEL chart AT the deepest point (special case), reducing it to:
(A) the chart gives `rlctAt(deepest) = nReg/2 + rlctAtOn(residual q(0,·)²) t0` — mechanical from the
    banked chart + quasi-split, AND
(B) `rlctAtOn(residual q(0,·)² at deepest) = lambdaCore(H − r)` — the residual's RLCT equals the
    closed-form core?
— thereby REPLACING the heavy gauge-slice with {chart + quasi-split + (B)}? Or does (B) itself reopen the
same heavy gauge-slice / recursion, making the chart route no easier?

Sub-questions:
Q1. At the DEEPEST point specifically, is the §SEL residual `q(0,·)` literally (or up to a measure-
    preserving/diffeo reindex) the REDUCED-WIDTH loss `dlnLoss (H−r) 0` (the `∏ C'_s` core in the
    docstring)? I.e. does the selected-minor chart's complement coordinates at the deepest point coincide
    with the reduced-core block `T_s`? If yes, (B) becomes "rlctAtOn(dlnLoss (H−r) 0) 0 = lambdaCore(H−r)"
    — the SAME reduced-loss-RLCT identity the gauge-slice route produces. If the chart's `q` is NOT the
    clean reduced loss (e.g. it's the reduced loss PLUS chart cross-terms), is the difference RLCT-
    irrelevant (germ-locally same zero-set / same Newton polytope) or does it genuinely change the core?
Q2. Is `rlctAtOn(dlnLoss M 0) 0 = lambdaCore M` (the reduced-core identity) ALREADY a separate theorem in
    this development (the recursion / R1 machinery computes lambdaCore), so that the chart route closes
    #44 by CITING it — or is that identity ALSO open / IS effectively #44 at smaller width (so the chart
    just shifts the wall down a level)?
Q3. The chart gives `rlctAt = rlctAtOn(...)` as an EQUALITY (both ≤ and ≥) only if Φ is a genuine local
    diffeo with the residual form holding as a germ identity (f =ᶠ F∘Φ). The §SEL producer was built to
    give the `≥`-leg of a COMPARISON (rlctAt deepest ≤ rlctAt v) CONSUMING #44 as `hDeepest`. Does the
    chart actually yield the ABSOLUTE deepest value as an equality, or only one inequality direction?
    (If only ≤, #44 needs the matching ≥ — is that the hard half?)
Q4. VERDICT: BOUNDED-via-chart (#44 = chart + quasi-split + a CITED reduced-core identity, modest LoC) vs
    RESEARCH-WALL (the chart route reopens the gauge-slice or an open recursion, no easier than the heavy
    route). If bounded, the minimal lemma chain. If wall, the one obstruction that doesn't dissolve.

Adversarial: I suspect the chart elegantly delivers (A) but (B) just renames the heavy content (the
reduced-core RLCT = lambdaCore is the actual mathematical work, and the chart doesn't compute it). Tell me
if that suspicion is right, or if there's a genuine reduction I'm missing (e.g. the deepest residual being
exactly a smaller-width deepest loss makes #44 INDUCTIVE on width via the chart — which WOULD be a real
win). Findings only, no Lean.
