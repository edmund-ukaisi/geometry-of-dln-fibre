<task>
Lean/Mathlib RLCT (real log-canonical threshold) proof for deep linear networks. I'm designing the
LAST piece of a "deepest point has minimal local RLCT" theorem and need to decide between two routes.

SETUP. Deep linear net: L matrix factors C_1...C_L (C_s : H_s × H_{s+1}). Loss = ‖C_1···C_L − B‖²_Frob
(squared Frobenius), B a fixed target of rank r. optimalSet = the global minimisers = the fibre
{∏C_s = B} (loss 0 there). "deepest point" = a specific minimiser where every layer has rank EXACTLY r
(the most degenerate / most singular minimiser). rlctAt(F, p) = sSup{ c≥0 : |F|^{-c} locally integrable
near p } (the team's own def; bigger = milder singularity).

GOAL (the ≥-leg): rlctAt(loss, deepest) ≤ rlctAt(loss, v) for ALL v ∈ optimalSet.

WHAT'S PROVEN. The "core comparison" core-P1: for the B=0 HOMOGENEOUS core F0 = ‖∏C_s‖², the origin
(deepest of the core) has rlctAt(F0, 0) ≤ rlctAt(F0, v0) for all v0 in the core fibre — proven LIGHT
from the rlctAt def (the ∃U∈𝓝 structure: an admissible nbhd of 0 swallows nearby ray points; + scaling
homogeneity). NO Mathlib analytic gap, no citation.

WHAT'S MISSING (the bridge from core-P1 to the full-B statement). The full-B loss is NOT homogeneous
(the −B breaks scaling), so core-P1 doesn't apply directly at a general v. The proposed bridge:
"L2-at-general-v": rlctAt(loss, v) = n_v/2 + rlctAt(core, v_core), i.e. CHART each v, peel a regular
(Morse, nondegenerate-quadratic) part of dimension n_v, leaving a core; then core-P1 compares the cores.
The subtlety: fibre points v are NON-rank-exact (their layers have VARYING ranks, not all rank r) —
e.g. for (2,2,2), r=0, a minimiser A1=[[1,0],[0,0]], A2=[[0,0],[0,1]] has both layers rank 1 (not 0).
At such a v the loss has a Morse-leading structure: the product-residual generators P_ij split into
leading-LINEAR (smooth → regular n_v/2) + a residual core. (At THAT example the residual core turned
out TRIVIAL: the 3 independent linear generators cut the fibre out smoothly, the 4th generator P10 lies
in their ideal, so rlctAt(v)=3/2=rlctAt(deepest) — TIGHT, v is a smooth fibre point.)

TWO ROUTES I'm deciding between:
 (R-chart) Build the broader-split chart at general v (Morse splitting lemma keyed on the Jacobian rank
   of the residual generator map at v) — extends the deepest's rank-r gauge-slice chart to arbitrary v.
   Heavy: needs the chart to exist + the n_v to be constant on optimalSet + the core to match.
 (R-LB) A cheaper DIRECT lower bound rlctAt(v) ≥ rlctAt(deepest) WITHOUT charting v — via some
   domination / monotonicity. The team has a BANKED lemma rlctAt_mono: if |G| ≤ |F| near a point AND
   (G=0→F=0) there, then rlctAt(G) ≤ rlctAt(F) [two functions, ONE point]. D1 is ONE function (the loss),
   TWO points (deepest vs v) — so rlctAt_mono doesn't apply directly.
</task>

<output_contract>
Terse, decisive:
1. Is there a DIRECT lower-bound route rlctAt(loss,v) ≥ rlctAt(loss,deepest) that AVOIDS charting v? In
   particular: can a clever choice of comparison function G near v (with |G|≤|loss| near v, G=0→loss=0)
   have rlctAt(G,v) = rlctAt(loss,deepest)? Or is the "two-points" obstruction fundamental — must we
   transport the deepest's germ to v somehow? If a direct route exists, sketch the comparison function.
2. If (R-chart) is needed: is n_v (the regular Morse dimension at v) CONSTANT over optimalSet? Argument
   for/against. (If it varies, the bridge "rlctAt(v)=n_v/2 + core" with constant shift FAILS — what
   replaces it?) Key worry: a non-rank-exact v might have MORE regular directions (smoother) than the
   deepest, making rlctAt(v) > rlctAt(deepest) but via a DIFFERENT decomposition.
3. The cleanest statement of "L2-at-general-v" that (i) holds for non-rank-exact v, (ii) feeds the
   core-P1 comparison. Is it really "n_v/2 + core(v_core)" with the SAME core dlnLoss(H-r)0, or does
   the core itself depend on v's stratum?
4. The deepest insight: WHY is the deepest (all-layers-rank-r) the minimal-RLCT point? Is it because it
   has the FEWEST regular directions (most degenerate), so n_deepest ≤ n_v and the cores compare? State
   the mechanism cleanly.
5. Most likely way the (R-chart) bridge is WRONG / incomplete.
</output_contract>

<grounding_rules>
The block algebra, the (2,2,2) example (v smooth, rlctAt(v)=rlctAt(deepest)=3/2), core-P1 (proven), and
rlctAt_mono (banked, two-functions-one-point) are TRUSTED. Reason about the route choice. Distinguish a
GERM/local claim from a global one. If the direct LB needs the same germ-transport as the chart, say so
(then R-chart is unavoidable). Flag if n_v varies — that's the load-bearing risk.
</grounding_rules>
