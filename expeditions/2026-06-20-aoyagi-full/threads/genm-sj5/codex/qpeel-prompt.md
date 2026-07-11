<task>
A soundness / faithfulness check on the STATEMENT of a Lean finiteness theorem (an RLCT / integrability
bound for deep linear networks). HUNT for a hidden defect that would let the statement be provable while
MISSING the true integrability threshold (a "collapse" masked by a too-weak hypothesis or an implicit
deletion). Do NOT rubber-stamp.

CONTEXT. The true math (verified elsewhere): on a rank-stratified cell with q collapsing directions, the
front loss reduces to a coupled corner. The threshold is the ADD of charges `c' < ½·Σ_i(h_i+1)` (NOT the
min `min_i (h_i+1)/2`, which is an undershoot from treating the collapsing directions independently). A
vanishing "unit" `U_i→0` (a deep-data degeneration) is a GENUINE RLCT-collapse UNLESS integrated jointly
with a transverse product-rank charge `D_q` big enough (needs the deep-block codim ≥ the corner charge);
an a.e.-deletion of `{U_i=0}` would hide the collapse.

THE LEAN OBJECTS (verbatim shapes):

  qCornerSliceAtUnits q h U c'  :=  ∫_{u ∈ [0,1]^q}  (Σ_i u_i² · U_i)^(−c') · ∏_i |u_i|^{h_i}   du
     -- ADDITIVE corner: a SUM Σ_i u_i²·U_i over blocks.

  qCornerSliceAtUnits_le (PROVEN):  for weights w_i≥0, w_i≤1, Σw_i=1, and U_i>0,
     qCornerSliceAtUnits q h U c'  ≤  (∏_i U_i^{−w_i c'}) · ∫_{u∈(0,1)^q} ∏_i |u_i|^{h_i − 2 w_i c'}  du
     -- q-ary weighted AM-GM: ∏(u_i²U_i)^{w_i} ≤ Σ w_i u_i²U_i ≤ Σ u_i²U_i, then (Σ)^{−c'} ≤ (∏)^{−c'}.

  qPeelIntegral q h m T c'  :=  ∫_{X ∈ ∏_i morseBox(m_i+1) T}  qCornerSliceAtUnits q h (fun i ↦ Σ_j (X_i)_j²) c'
     -- the units U_i = ‖X_i‖² are squared norms of FREE deep blocks X_i ∈ [−T,T]^{m_i+1}, integrated JOINTLY.

  qPeelIntegral_lt_top (the STATEMENT under audit; proof is a `sorry`):
     hyps:  (hcod : ∀ i, h_i ≤ m_i)  (0 < T)  (0 ≤ c')  (c' < (Σ_i (h_i+1))/2)
     concl: qPeelIntegral q h m T c'  < ⊤.

Answer, exactly:

Q1. Is the loss `Σ_i u_i²·U_i` genuinely the ADDITIVE (block-diagonal) corner, so the threshold is the
    ADD `½·Σ(h_i+1)`, NOT a shared-divisor / multiplicative form whose true threshold would be the MIN
    `min_i (h_i+1)/2`? Confirm the statement's threshold `c' < ½·Σ(h_i+1)` is the correct (ADD) one for
    this integrand and is NOT secretly the min.

Q2. THE GATE. Is `h_i ≤ m_i` the correct transverse-charge condition, and is it (a) NOT vacuous, (b) NOT
    too weak? Work the AM-GM route with the min-cut weights `w_i = (h_i+1)/Σ(h_j+1)`: the u-monomial box
    integral `∫_{[0,1]^q} ∏|u_i|^{h_i − 2 w_i c'}` is finite iff `∀i, 2 w_i c' < h_i+1`; each deep block
    `∫_{[−T,T]^{m_i+1}} ‖X_i‖^{−2 w_i c'}` is finite iff `2 w_i c' < m_i+1`. Check: for `c' < ½·Σ(h_j+1)`,
    does `2 w_i c' < h_i+1 ≤ m_i+1` hold (so BOTH bind together, under `h_i ≤ m_i`)? Does violating
    `h_i ≤ m_i` (i.e. `h_i > m_i`) make the deep integral DIVERGE below the additive threshold (a genuine
    collapse the gate prevents)? Is `h_i ≤ m_i` exactly right, or should it be strict / different?

Q3. THE {U_i=0} LOCUS. The units `U_i = ‖X_i‖²` vanish on `{X_i = 0}` (a codim-(m_i+1) locus IN the
    integration domain). Is this integrated JOINTLY (the deep-Morse block integral captures the
    `{X_i → 0}` neighborhood) rather than a.e.-DELETED? Note the AM-GM lemma needs `U_i > 0` (a.e., since
    `{X_i=0}` is null) — is applying it a.e. and integrating the deep block over the FULL box the sound
    route, or does the `{X_i=0}` null set hide a positive-measure divergence? (I.e. is the divergence, if
    any, on the null exact-zero set or on its positive-measure neighborhood?)

Q4. Any OTHER hidden defect in the STATEMENT shape: a weight-drop, an implicit finiteness assumption, a
    measure mismatch (free-Lebesgue deep boxes vs the intended product measure), the rpow-of-0 convention
    `(0)^{−c'}` masking a divergence, or the threshold being off (should it be `½·Σ(h_i+1)` or something
    else)? Is the statement's use of FREE Morse boxes for the deep data (Lebesgue) sound, given the true
    charge is a product-rank codim?
</task>

<output_contract>
For each Q1-Q4: PASS (the statement faithfully encodes the ADD-not-MIN + joint transverse-charge + no
a.e.-deletion, no hidden defect) or a PRECISE issue. State whether `h_i ≤ m_i` is the exactly-right gate.
Flag any upstream obligation (a correct instantiation the abstract statement relies on) even if the
statement itself is sound.
</output_contract>

<grounding_rules>
Exact algebra (the AM-GM + Beta/Morse integrals). Work the min-cut-weight balance explicitly. Do NOT
assume the statement is sound — hunt for the masked collapse. Distinguish a defect IN the statement from
an upstream obligation on the caller.
</grounding_rules>
