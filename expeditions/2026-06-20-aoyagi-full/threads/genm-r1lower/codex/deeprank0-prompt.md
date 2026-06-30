<task>
Deep linear network (DLN) RLCT formalisation, depth L=2. I must determine if a degenerate achiever
stratum diverges at EXACTLY the headline rate, or report a mismatch (kill-condition).

SETUP. L=2 network: weights (W0 : H1×H0, W1 : H2×H1, W2 : H3×H2) with hidden widths H, and a
dimension vector M : Fin 3 → ℕ = (M0,M1,M2) = the COMPRESSED ranks / achiever-center block sizes. The
multiplication-map fiber RLCT lower-bound atom needs, for the achiever center:
    ∫_{[−ε,ε]^N} |routeMCore(x)|^{−c'} dx = ⊤  for all c' ≥ ½·minAdm(M), all ε>0,
where routeMCore is the (square Frobenius) loss germ at the achiever center and N = ambient param dim.

THE STRATUM. deepRank(M) := Text(tach)(2) = the compressed leaf rank along the achiever path. The
achiever path argmin tStar is unique = ![0,0] for M=(1,1,2) (Mval ![0,0] = M0·M1 = 1 < Mval ![1,0] = 2),
so deepRank = tStar 0 = 0. This is genuinely InteriorDrop (interiorDrop_L2_iff: 0<M2 ∧ deepRank<M0 ∧
deepRank<M1 = 0<2∧0<1∧0<1, TRUE) and EXCLUSIVE from clean/smeared. minAdm(M) = ∑ rBlock·cBlock =
(M0−0)(M1−0) + (tStar0−tStar1)(M2−tStar1) = M0·M1 + 0 = M0·M1. So for M=(1,1,2): minAdm = 1·1 = 1,
headline rate ½·minAdm = ½.

THE EXISTING interior chart (which I built) requires h0r : 0 < deepRank — it binds a "leaf pivot"
coordinate that does not exist when deepRank=0 (the leaf K-block is vacuous). So deepRank=0 needs a
SEPARATE handler. The lead's read: at deepRank=0 the leaf K-block is empty and the loss collapses to a
simple monomial-times-regular form; e.g. for (1,1,2): loss germ ≈ w0²·w1²·‖W2‖² (a product of scalar
blow-up coords w0,w1 and a regular factor).

KILL-CONDITION (the decisive check). At the deepRank=0 achiever center, does the box integral
∫|loss|^{−c'} diverge at EXACTLY c' = ½·minAdm = ½·M0·M1 (the same exponent the headline needs), via a
radial/monomial blow-up? Work out the deepRank=0 collapsed loss form for GENERAL (M0,M1,M2) at L=2
(not just (1,1,2)), identify the blow-up monomial det exponent, and check the divergence threshold of
∫ |det Dφ|·|loss∘φ|^{−c'} matches ½·M0·M1. If the exponent does NOT match ½·M0·M1, that is a real
issue — report the precise mismatch.

PRONG (ii) chart sketch: at deepRank=0 the deepest compressed rank is 0, so the achiever center is the
ORIGIN of the deepest factor block; the normal directions are the full M0·M1 entries of the
rank-(M0×M1) block (the "E-block", no leaf pivot). Is the divergence then a PURE radial blow-up on
these M0·M1 coords (det exponent M0·M1 − 1, loss ~ r²·V), giving threshold (M0·M1)/2 = ½·minAdm —
i.e. structurally the SAME as the BoundaryClean whole-deepest radial, just at a deepest block of size
M0·M1 with the leaf rank collapsed? If so, the deepRank=0 interior handler may be a thin specialization
of the banked clean radial (RouteM4422-style), NOT new chart math.
</task>

<output_contract>
1. KILL-CONDITION VERDICT: does deepRank=0 diverge at EXACTLY ½·minAdm = ½·M0·M1? YES with the rate
   computation, or NO with the precise exponent mismatch. This is decision-critical — be rigorous.
2. The collapsed loss form at deepRank=0 for general (M0,M1,M2), and the blow-up that realizes the rate.
3. BOUNDED vs WALL: is the deepRank=0 handler (a) a thin specialization of the banked whole-deepest
   radial clean chart (pivotBlowupOn on the M0·M1 E-block, det |u_p|^{M0·M1−1}), (b) the smeared square
   chart with r=0, or (c) genuinely new chart math? Rank by cheapness.
3. Distinguish proven-arithmetic from inference. Flag anything you're unsure of.
</output_contract>
