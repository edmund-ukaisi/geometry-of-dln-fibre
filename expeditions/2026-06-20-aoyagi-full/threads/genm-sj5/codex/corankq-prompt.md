<task>
An exact RLCT / integrability question about a coupled "corner" blow-up in a resolution for deep linear
networks. Adjudicate adversarially — HUNT for an RLCT-COLLAPSE (the coupled sum secretly behaving like a
min, undershooting the intended threshold). Do NOT reassure.

SETUP. On a rank-stratified cell (corank exactly q: q singular values of a matrix collapse, the rest
bounded below), a front integral reduces to a coupled corner monomial integral. For corank 2 the exact
model (verified elsewhere) is
  I = ∫_{[0,1]²} (u₀²·U₀ + u₁²·U₁)^{−c'} · |u₀|^{a₀} |u₁|^{a₁} du₀ du₁,   U₀,U₁ > 0 "units",
with (a₀,a₁) = (3,2). The corner blow-up u₁ = u₀·τ gives |u₀|^{a₀+a₁+1}|τ|^{a₁} and loss u₀²(U₀+τ²U₁), so
  ∫ u₀^{a₀+a₁+1−2c'} du₀ < ∞  ⟺  c' < (a₀+a₁+2)/2 = (3+2+2)/2 = 7/2.
The charges ADD (a₀+a₁+1 = 6). By contrast the INDEPENDENT-divisor caricature (u₀u₁)²·U gives
min((a₀+1)/2,(a₁+1)/2) = min(2,3/2) = 3/2 — an undershoot. The intended per-cell threshold is
½(D_q + d_q) where d_q = m(r−q) is the stable-block Morse charge and D_q is a product-rank tube codimension
(for the concrete (3,3,3,4) case: (D_q,d_q) = (8,6),(4,3),(1,0) for q=1,2,3, thresholds 7/2,7/2,4).

Answer, exactly:

Q1. Generalize the coupled corner to corank q (q collapsing radials u₀,…,u_{q−1} sharing the corner
    {u₀=…=u_{q−1}=0}, weights → 0; one stable block, weight ≥ κ²). With per-radial Jacobian powers a₀,…,a_{q−1}
    (a_i = block_dim_i − 1) and loss order 2, iterate the corner blow-up. Does the threshold come out as
    ½(Σ_i (a_i+1)) = ½·(total charge), i.e. the charges ADD (NOT min)? Give the iterated-blow-up bookkeeping
    and the exact threshold. Confirm it equals ½(D_q+d_q) for the (3,3,3,4) cells.

Q2. ★ THE RLCT-COLLAPSE HUNT. The crude caricature z²(x²+y²) (a shared 1-dim z times a 2-dim sum)
    RLCT-collapses: its RLCT is ½, BELOW the "disjoint" value 1. Does the DLN coupled corner
    (u₀²U₀+u₁²U₁ etc.) similarly collapse below ½(Σ(a_i+1)) when the "units" U_i are NOT constant — in
    particular, when a U_i → 0 (a stable direction ALSO starts to collapse)? Precisely: is
    ∫(u₀²U₀+u₁²U₁)^{−c'}|u₀|^{a₀}|u₁|^{a₁}, with U₀ or U₁ allowed to vanish on a sublocus, still governed by
    the ADD threshold, or does the U_i→0 locus lower the RLCT (a genuine collapse)? If it lowers it, EXHIBIT
    the collapse; if not, show why (e.g. the U_i→0 locus is a HIGHER-codim stratum carrying its own,
    strictly-larger, threshold — the recursion q→q+1). Is the recursion (assign {U_i=0} to corank q+1)
    well-founded and does it AVOID the collapse?

Q3. The stable-block units U_i (= the top r−q singular-value directions, weight κ²) are bounded below by
    κ² BY THE CELL DEFINITION (corank exactly q ⟹ σ_{r−q} ≥ κ). Where a stable direction drops (σ_{r−q} < κ)
    one leaves the cell into corank q+1. Confirm: (a) on the OPEN cell the coupled-corner threshold is
    exactly ½(D_q+d_q) (units bounded below, no collapse); (b) at the cell boundary σ_{r−q}→κ the corank-q
    estimate CONTINUOUSLY matches the corank-(q+1) estimate (no gap/collapse at the seam); (c) the whole
    box = ⊔_q cell_q, Σ_q ∫_{cell_q} < ∞ for c' < min_q ½(D_q+d_q) = ½·minAdm.

Q4. Is there any q where the coupled corner does NOT give ½(D_q+d_q) — e.g. a mismatch between the corner
    charge Σ(a_i+1) and D_q+d_q, or a genuine collapse from the pushforward measure on the collapsing
    singular values? (The measure on the collapsing σ's is the product pushforward, not Lebesgue.)
</task>

<output_contract>
For each Q1-Q4: PROVEN/DERIVED exact statement (mark inference vs fact). The iterated corank-q corner
threshold as ½(total charge). A clear YES/NO on whether an RLCT-collapse occurs when a unit U_i→0, with
the exhibited collapse if yes, or the well-founded recursion q→q+1 (assigning {U_i=0} to the deeper cell)
if no. The seam-continuity across the cell boundary. Any q where ½(D_q+d_q) fails.
</output_contract>

<grounding_rules>
Exact algebra (iterated radial/corner blow-up, Beta integration). MC only to guide. Treat the units U_i as
possibly-vanishing on subloci and track where the RLCT is governed. Do NOT read my expectation into the
answer — hunt for the collapse; if the coupled corner is sound, prove it; if it collapses, exhibit the
witness.
</grounding_rules>
