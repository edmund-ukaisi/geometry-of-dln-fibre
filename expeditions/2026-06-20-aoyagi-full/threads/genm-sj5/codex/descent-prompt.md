<task>
A build-architecture adjudication for the deepest analytic step of an RLCT finiteness proof (deep linear
networks). Decide which of two routes closes a specific integral, and resolve a "zero-slack / Hölder-
infeasible" concern. Be adversarial about the zero-slack point — do NOT wave it away.

SETUP. A "front peel" of a matrix-product loss produces the FREED-Γ TRIPLE integral (to be shown finite):
  I(c') = ∫_{A'} ∫_{x} ∫_{Γ}  (freedSchurLoss x Γ Q)^{−c'},   Q = A₁·A₂ (the tail PRODUCT, from A'),
  freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b),   Q_b = Y·A₂ (Y = corank rows of A₁),
  P = pivot (invertible on chart), Q̃ₚ = sheared pivot rows, Γ = freed corank block, x = front data.
The target: I(c') < ∞ for c' < ½·minAdm(M), M=(3,3,3,4), ½·minAdm=7/2.

THRESHOLD ARITHMETIC (verified): peelCharge = (M₀−t)(M₁−t) = 4 at t=1; redChain = (t,M₂,M₃)=(1,3,4),
minAdm(redChain)=3. Binding cut: minAdm(M) = peelCharge + minAdm(redChain) = 4+3 = 7 (ZERO SLACK). The
decoratedPeelStep architecture: reduce I(c') to the reduced-chain IH `hIH(redChain)` at the threshold
SHIFTED by ½·peelCharge — i.e. finiteness for c' − ½·peelCharge < ½·minAdm(redChain), giving
c' < ½·peelCharge + ½·minAdm(redChain) = 2 + 3/2 = 7/2.

A front-first "self-contained" attempt (spectral diagonalization + a front-ONLY radial blow-up, treating
the deep product Q as fixed) UNDERSHOOTS (threshold ≈3, not 7/2) — it misses the deep A₂ layer.

TWO CANDIDATE ROUTES for I(c') < ∞:
- Route A (IH recursion): integrate the outer tail A', apply a UNIT-JACOBIAN change of variables that
  reduces the deep product Q_b = Y·A₂ to the reduced chain's zero-product locus (a "normal slice" CoV,
  measure-preserving), descend a monomial "ledger" to a monomial terminal, and CLOSE on the reduced-chain
  box-finiteness IH `hIH(redChain)` at the shifted exponent.
- Route B (fresh full-deep blow-up): a self-contained blow-up of the whole deep, not reusing the IH.

THE ZERO-SLACK CONCERN (a design cert flagged, must adjudicate): at the binding cut the residual exponent
c' − ½·peelCharge EXACTLY saturates the reduced-chain IH threshold ½·minAdm(redChain) as c' → ½·minAdm(M).
The cert claims: the freed residual carries a COUPLED weight (the pivot energy w = frobSq(P·Q̃ₚ), and the
reduced coupling), so applying `hIH(redChain)` as a BLACK BOX to `∫ w-weighted (reduced loss)^{−s}` is
Hölder-infeasible at zero slack (no ε to spare to absorb the unbounded w-weight). The cert's verdict:
"bounded, not a wall, unbuilt double induction."

Answer, exactly:
Q1. Is the threshold split correct: I(c')<∞ for c'<7/2 = ½·peelCharge + ½·minAdm(redChain), with the deep
    layer's contribution being ½·minAdm(redChain)=3/2 (the IH), and the front-only undershoot omitting it?
Q2. Which route (A or B) is the tractable + faithful path? In particular: does the UNIT-JACOBIAN normal-
    slice CoV (Route A) STRAIGHTEN the coupled w-weight so the reduced problem is a genuine box integral
    of the reduced chain (making the IH applicable at the STRICT shifted threshold, c'−½peelCharge <
    ½minAdm(redChain) strictly), thereby RESOLVING the zero-slack/Hölder concern — OR does the coupling
    survive the CoV, genuinely requiring the decoration to be CARRIED (a real double induction)?
Q3. THE ZERO-SLACK ADJUDICATION. Is the plain reduced-chain IH `hIH(redChain)` SUFFICIENT (given the CoV
    straightens the coupling and the strict inequality c'<½minAdm(M) gives strict c'−½peelCharge<
    ½minAdm(redChain)), or is it genuinely INSUFFICIENT as a black box (the coupled weight blocks it even
    with the CoV)? If insufficient, what exactly must be carried (the "decoration"), and is it still bounded
    labour (a monomial-ledger descent to a terminal), not a wall?
Q4. The interface: the conditional inner-Γ finiteness needs three hyps that FAIL pointwise — (i) pivot
    energy w>0 (fails on a null locus {Q̃ₚ=0}), (ii) Q_bQ_bᵀ PosDef (fails on the rank-deficient/bottleneck
    charts), (iii) c'>a·b/2 (fails on ~94/480 charts). How does the descent supply these as a MEASURE
    statement (integrate A')? (Candidate: rank-stratified cell cover for (ii); a sub-critical bounded
    branch for (iii); joint integration for (i).) Is that the right structure?
</task>

<output_contract>
Q1: confirm/correct the split. Q2: A or B + the CoV-straightens-or-not verdict. Q3: the zero-slack
adjudication — IH sufficient (with the CoV + strictness) or genuine double-induction, and if the latter
whether still bounded labour. Q4: the measure-statement structure for the 3 failing-pointwise hyps. Mark
inference vs derived; flag anything that looks like a wall.
</output_contract>

<grounding_rules>
Exact reasoning. The key pivot is whether the unit-Jacobian normal-slice CoV converts the coupled freed
residual into a clean reduced-chain box integral (IH applicable) or leaves a coupled weight (double
induction). Adjudicate that specifically. Do NOT assume the IH suffices; do NOT assume it fails — reason it.
</grounding_rules>
