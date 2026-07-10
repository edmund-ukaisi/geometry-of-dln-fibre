<task>
I am formalising (Lean4/Mathlib) a measure-theoretic finiteness lemma and need a decorrelated
judgement on WHETHER it can be closed with the currently-banked machinery, or whether it genuinely
requires an unbuilt multi-step recursion. Give me a truth-value + the cheapest honest deliverable.

## The target (single open `sorry`, `sjJointResolution`)

For a width vector `M : Fin (L+3) → ℕ` (a deep-linear-network layer chain of L+3 widths), define
`gammaPeelIntegral M t ρ κ c'` (t = pivot rank at boundary 0; ρ,κ pivot row/col embeddings) — the
per-pivot-chart contribution to the layer-product box integral:

  gammaPeelIntegral M t ρ κ c'
    = ∫_{A' ∈ box(tailChain M)} ∫_{A0 ∈ matBox(M0,M1) ∩ pivotChart ρ κ}
        frobSq(A0 · prod(tailChain M) A')^{−c'}

where tailChain M = (M1,M2,…,M_last) (arity L+2), prod = layer product, frobSq = squared Frobenius
norm, matBox = [−1,1]-cube, pivotChart ρ κ = {A0 : its t×t (ρ,κ)-minor is a unit}.

GOAL: prove `gammaPeelIntegral M t ρ κ c' < ⊤` GIVEN
  - hIH : ∀ M' : Fin (L+2)→ℕ, RouteMBoxThresholdFinite M'   (box-finiteness for EVERY one-shorter chain)
      where RouteMBoxThresholdFinite M' := ∀ c'' < minAdm(M')/2, ∫_{box} frobSq(prod M' ·)^{−c''} < ⊤
  - 1 ≤ t ≤ min(M0,M1),  c' < minAdm(M)/2.

`minAdm` satisfies the recursion  minAdm(M) = min_{0≤t≤min(M0,M1)} [(M0−t)(M1−t) + minAdm(redChain t M)],
with redChain t M = (t, M2, …, M_last) (arity L+2), base minAdm(a,b)=a·b. Banked:
`sjChargeBudget_le`: minAdm(M) ≤ (M0−t)(M1−t) + minAdm(redChain t M) for all admissible t;
`minAdm_le_minAdm_tailChain`: minAdm(M) ≤ minAdm(tailChain M).

## What IS banked (confirmed present, sorry-free)

1. EQUALITY (`gammaPeelIntegral_sjGoodMap_eq'`): gammaPeelIntegral rewrites EXACTLY to
     ∫_{A'} ∫_{x∈outerDom} ∫_{Γ} (sjGoodChartLoss x Γ Ã₁ A₂)^{−c'}
   where x=(P,B12,C) are A0's non-corank blocks (P = t×t invertible pivot on the chart), Γ = A0's
   corank block ((M0−t)×(M1−t)), Ã₁ = (A'0 row-reindexed) : (Fin t ⊕ Fin(M1−t)) × M2, A₂ = deep
   product : M2 × M_last. sjGoodChartLoss = frobSq(P·v·A₂)+frobSq((C·v+Γ·W)·A₂), v = pivot rows of Ã₁
   (shifted), W = corank rows of Ã₁ (b×h = (M1−t)×M2).
2. Transport atoms (steps a/c): Pi-split of A' into (A'0, deeper) with deep factor A₂ = fn(deeper only);
   pivot-row → free-v translation (measure-preserving). Step (b) (row-split of A'0 into pivot × W) is
   the only un-built transport atom (fiddly reindex, no API wall claimed).
3. ENDPOINT (`sjGoodChartLoss_endpoint_lt_top`): ∫_{matBox a b 1 ×ˢ matBox t h 1}
     (sjGoodChartLoss x y1 (assembleFront x y2 W) A₂)^{−c'} < ⊤,
   REQUIRING: P LEFT-invertible (holds on chart), W RIGHT-invertible (W·RW=1), A₂ RIGHT-invertible
   (A₂·RA=1), c' < (a·b + t·h)/2 = ((M0−t)(M1−t) + t·M2)/2.
4. Corank Γ-blowup atom (`corankBlock_morsePeel_lt_top` / `gammaAtom_aniso_shifted_eq`): for Q_b of
   FULL ROW RANK (Q_b Q_bᵀ PosDef) and c' > pq/2, ∫_Γ (w + ‖Apiv‖² + ‖Ccross+Γ·Q_b‖²)^{−c'}
     = det(Q_bQ_bᵀ)^{−p/2}·Cresid·(w+‖Apiv‖²+‖Ccross(1−proj)‖²)^{−(c'−pq/2)}  (EXACT).
5. Fibre engine (`fibre_lintegral_mul_le`): ∫_{X∈matBox p n T} frobSq(X·Y)^{−c'} ≤ fibreConst·frobSq(Y)^{−c'}
   for 0<c'<p/2 (p = #rows of X), fibreConst finite & Y-independent.

## What I found (please stress-test)

(a) The naive route "bound the chart by the full box, then fibre-engine down to routeMLayerBoxIntegral(tailChain M),
    then hIH(tailChain M)" FAILS the threshold: it caps at c' < M0/2, but minAdm(M) > M0 happens
    (e.g. M=(1,2,2): minAdm=2, M0=1; 417 violations for L=3..5, widths in 1..4). So the pivot chart is
    essential — discarding it loses the needed threshold room.
(b) The ENDPOINT (banked) requires W ((M1−t)×M2) and A₂ (M2×M_last) RIGHT-invertible. When M1−t > M2 or
    M2 > M_last this is dimensionally IMPOSSIBLE (more rows than cols → no full row rank), and even when
    dims allow it fails on a positive-measure rank-deficient set. So the endpoint closes only a
    "dimensionally-cooperative + generic" branch.
(c) THREE separate banked-module docstrings independently state that closing `sjJointResolution` requires
    a well-founded (S,J) DOUBLE-induction recursion that is "~65-75% genuinely-new, UNBANKED, multi-tide"
    and "stays the single named analytic sorry, UNTOUCHED, until the recursion genuinely lands"
    (RouteMSJDecorated); "discharge the OUTER A'-integral carrying the Gram residual det(Q_bQ_bᵀ)^{−p/2}
    and shifted core — the (S,J) double induction, the standing gap" (RouteMSJCorankPeel).
(d) BUT a recent handoff (from the thread that banked the transport atoms) claims 803 closes as pure
    "labour, no wall" via: transport (a+b+c) to endpoint coords, then "good/deeper cover: matBox∩pivotChart
    = good{|det pivot minor|≥δ} ∪ deeper; good closes by endpoint; deeper NON-binding by sjChargeBudget_le;
    L-recursion over the rank flag uses hIH on STRICTLY-SHORTER chains (redChain/tailChain)."

## The sharp questions

Q1. Is the handoff (d) correct that hIH on redChain/tailChain closes the DEEPER branch (where W or A₂ is
    rank-deficient), WITHOUT building the (S,J) recursion? Specifically: the deeper branch integrand still
    couples Γ to a rank-deficient Q_b; the corank atom (banked) needs FULL row rank. To reduce the deeper
    branch to `routeMLayerBoxIntegral(redChain t M)` (so hIH applies) one must re-express the deeper
    integral as a shorter-chain box integral — is that reduction a single measure-preserving/monotone step,
    or does it require re-running the Schur peel at the next boundary (i.e. IS the recursion)?
Q2. Is my reading (c) correct that the general-L close is the unbuilt multi-tide recursion, making the
    handoff (d) over-scoped?
Q3. Given a SINGLE formalisation tide (bounded, ~hundreds of lines), what is the highest-value HONEST
    deliverable: (i) build the transport composition (step b + compose a+b+c) as a sorry-free reusable
    EQUALITY landing gammaPeelIntegral in the v-exposed ∫_{env}∫_{(Γ,v)} form, isolating the finiteness as
    a named lemma; or (ii) attempt a good/deeper cover + hIH close directly; or (iii) something else?
    Rank them.
</task>

<output_contract>
Four sections, terse:
1. Q1 verdict (YES hIH closes deeper / NO it is the recursion) + the single crux reason.
2. Q2 verdict (is (c) right, is (d) over-scoped) — one paragraph.
3. Q3 ranked deliverables (1st/2nd/3rd) with one line each on why.
4. If NO to Q1: the single most-likely-overlooked shortcut that COULD close it (name the mechanism), or
   state "none — it is the recursion."
Flag every claim as [inferred] vs [from the facts I gave].
</output_contract>

<grounding_rules>
You have only what I wrote above — do not assume other Mathlib lemmas exist. If a step needs a lemma I
did not list as banked, say so explicitly and treat it as unbuilt. Distinguish "measure-theoretically
true" from "reachable with the listed banked pieces."
</grounding_rules>
