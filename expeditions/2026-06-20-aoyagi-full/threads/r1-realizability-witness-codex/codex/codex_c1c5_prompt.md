<task>
I am deciding whether ONE Lean datum structure can serve two related but distinct local resolutions in
an RLCT (real log-canonical threshold) recursion, or whether two structures are forced. Derive from the
definitions; distinguish FACT from INFERENCE. Exact algebra only if you compute.

THE DATUM (a Lean structure, call it Datum) carries, for a node:
  - flatCore : (Fin nReg → ℝ) × Y → ℝ        (the node's local loss core near the deepest point (0,0))
  - G : Y → ℝ                                 (the reduced-chain core; G² = the smaller chain's loss)
  - constants c₁,c₂ > 0
  - a SQUEEZE field:  near (0,0),  c₁·Φ ≤ flatCore ≤ c₂·Φ,  where  Φ = (∑_{j<nReg} w.1_j²) + G(w.2)².
The datum's CONSEQUENCE (a proven theorem) is:  rlct(flatCore, (0,0)) = nReg/2 + rlct(G², 0).
So Φ has TWO parts: a regular block of nReg literal coordinate-squares, and the single reduced core G².

TWO NODE TYPES feed this datum:
  (C1) "hard-pivot" node: flatCore = (∑_j E_j²) + ∑_{i,j} (b_i·E_j + SΓ_{ij})², with the pivot column b
       BOUNDED (∑ b_i² ≤ T², b→0 at the deepest point). The regular block is ∑E_j² (so nReg = #E),
       the reduced core is G² = ∑ SΓ². The squeeze holds with c₁=(2(1+T²))⁻¹, c₂=2+2T² (a bounded-linear
       -perturbation Young estimate). Here the defect lives in the PERTURBATION b·E, NOT in nReg.
  (C5) "partial-drop" node: a survivor block (rank b) plus a SINGLE rank-1 complement defect δ. The
       loss is  ∑‖G·p‖² (survivor) + ‖G·q + δ·e‖² (the complement column), e a bounded nonzero gauge
       vector. A shear δ' = δ + (G·q·e)/‖e‖² gives EXACTLY  loss = ‖e‖²·δ'² + [survivor core projected
       off e].  So the defect becomes ONE regular square ‖e‖²·δ'² (a Morse ½), and the survivor core is
       the reduced G². Here the defect lives in the REGULAR block nReg, NOT in a perturbation.
</task>

<output_contract>
Q1. Is the C1 node an instance of Datum? (state the field assignments: nReg, the regular block, G, c₁,c₂.)
Q2. Is the C5 node (after the shear) an instance of Datum? Specifically: can the C5 shear-split
    loss = ‖e‖²δ'² + (survivor core) be put in the form c₁·Φ ≤ flatCore ≤ c₂·Φ with Φ = (∑_{j<nReg} w.1_j²)
    + G², by COUNTING the δ'-direction (rescaled by ‖e‖, which is bounded in [c,C], 0<c≤C) as one of the
    nReg regular coordinates? What are c₁,c₂ then?
Q3. THE DECISION: does ONE Datum structure cover both C1 and C5, or are two structures forced? The
    difference is WHERE the defect sits: C1 puts it in the bounded perturbation b·E (squeeze constants
    ≠1), C5 puts it in the regular block nReg (squeeze constants =1 on that coordinate). Is that a
    difference of FIELD VALUES (same structure, different producer) or of STRUCTURE (different fields)?
Q4. Any obstruction to the unified datum? E.g. does counting δ' in nReg require ‖e‖ to be a CONSTANT
    (not a function of the survivor coords) for the squeeze constants to be uniform? If ‖e‖ varies over
    the chart in [c,C], does c₁·Φ ≤ flatCore ≤ c₂·Φ still hold with Φ using the UNWEIGHTED δ'² (i.e.
    absorb ‖e‖² into the squeeze constants)? Give the resulting c₁,c₂ in terms of c,C.
</output_contract>

<grounding_rules>
- Datum exactly as stated; the consequence rlct = nReg/2 + rlct(G²) is a theorem you may use.
- A nondegenerate quadratic in m variables has rlct m/2; a bounded unit u (0<a≤u≤b) does not change rlct.
- FACT vs INFERENCE explicit. Exact arithmetic if you compute.
</grounding_rules>
