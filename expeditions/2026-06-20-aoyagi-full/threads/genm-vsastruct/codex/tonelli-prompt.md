<task>
Adjudicate whether integrating a divergent fixed-parameter slice over a deep matrix RESCUES finiteness at a
target exponent, via codimension compensation — or whether the divergence locus is a genuine binding
deeper stratum. Exact algebra; I withhold my lean.
</task>

<setup>
A "corner slice" (fixed deep data) is
   S(U0,U1;c') = ∫∫_{[0,1]^2} u0^3 u1^2 (u0^2 U0 + u1^2 U1)^{-c'} du0 du1,
finite for c' < (3+2+2)/2 = 7/2 when U0,U1 > 0 (banked; weighted AM-GM, "codims add"). As a unit → 0 it
diverges (exact, MC-confirmed):
   S ≍ U1^{-(c'-2)}   as U1→0  (the u0-only corner threshold is (3+1)/2 = 2),
   S ≍ U0^{-(c'-3/2)} as U0→0  (the u1-only corner threshold is (2+1)/2 = 3/2).

The one-peel integral integrates S over the DEEP DATA. The units are
   U1 = a_piv^2 · ‖v̄ A2‖^2,     U0 = ‖w1 A2‖^2 + δ^2 ‖w2 A2‖^2,
where A2 is a free 3×4 matrix (the deep layer), v̄,w1,w2 are unit 3-vectors (blow-up units), a_piv,δ ≠ 0.
The zero loci:
   {U1=0} = {v̄ A2 = 0}   (v̄ A2 ∈ R^4, 4 linear conditions on A2; codim 4, MC-confirmed density ~ U1^1),
   {U0=0} = {w1 A2 = 0 ∧ w2 A2 = 0}   (8 conditions; codim 8),
   {A2=0}  (codim 12; both units ~ ‖A2‖^2 → S ≍ ‖A2‖^{-2c'}).
Target: does the joint integral ∫_{deep} S dμ close at c' = 7/2?
</setup>

<questions>
Q1 (the U1 rescue). Near {U1=0}, the joint integrand is S·(deep measure) ≍ U1^{-(c'-2)}·ρ(U1),
   ρ(U1) ~ U1^{d1/2 - 1} with d1 = codim{U1=0} = 4. For which c' does ∫_0 U1^{-(c'-2)}·U1^{d1/2-1} dU1
   converge? Give the threshold c' < 2 + d1/2. Is it > 7/2 (non-binding) or ≤ 7/2 (binding)?

Q2 (U0 and the deepest {A2=0}). Same for {U0=0} (d0=8, divergence exponent c'-3/2) and {A2=0} (codim 12,
   S ≍ ‖A2‖^{-2c'}). Give both thresholds. Which, if any, is ≤ 7/2 (would bind)?

Q3 (verdict + the correlation check). Conclude: does the A2-integration RESCUE the fixed-slice rank-drop
   divergence at 7/2 (so the binding 7/2 is the SECTOR slice itself, and the rank-drop is a NON-binding
   deeper stratum handled by codim compensation), or is some rank-drop stratum genuinely binding at 7/2
   (needing a separate deeper resolution)? Stress-test the CORRELATION: U0 and U1 both vanish on {A2 rank
   drop}; does the joint vanishing (both units small together) create a worse divergence than the separate
   estimates, i.e. could the intermediate {rank A2 = 2} locus bind even though {A2=0} does not?
</questions>

<output_contract>
For Q1–Q3: exact threshold + "FACT" vs "INFERENCE". End: is the one-peel joint finite at 7/2 with the
A2-rank-drop RESCUED (non-binding), or is there a binding deeper stratum — and if rescued, is the
rescue a Morse/norm-power integral ∫‖v̄A2‖^{-s} dA2 (< ∞ iff s < codim)?
</output_contract>

<grounding_rules>
Exact radial/codim algebra. Keep the fixed-slice divergence separate from the joint integral. Check the
correlation (both units vanishing together) explicitly — that is where a naive per-unit estimate could miss
a binding stratum.
