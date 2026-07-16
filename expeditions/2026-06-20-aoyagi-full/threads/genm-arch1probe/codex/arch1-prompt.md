<task>
Adjudicate two questions about an RLCT/integral-finiteness proof architecture for deep linear networks (DLN).
Setup: chain of widths M=(M0,M1,...,M_last); mult = product of the layer matrices; the "codim" minAdm(M)
is given by the recursion minAdm(M)=min_{t<=min(M0,M1)}[(M0-t)(M1-t)+minAdm(redChain t M)],
redChain t M=(t,M2,...,M_last) (one fewer layer); leaf minAdm(a,b)=a*b. deepTailMin(M)=min(M2,...,M_last).
"good" chains: deepTailMin(M) <= M1.

The box integral (finiteness target) is ∫_box ||mult||^{-2c'} for c'<minAdm(M)/2. A "peel" at the binding
cut t* (an argmin of the recursion) is followed by singular-value SHELLS j=0..r (r=min(M0-t*,M1-t*)) of the
DEEP TAIL product; the cut becomes u=t*+j. At each strict shell (1<=j<r) a head/row split exposes:
 - corank block Q_b = A_cor * Z_deep(z), where Z_deep is the product of the deep tail (M2,...,M_last),
   generic rank = deepTailMin(M); A_cor is (M1-u) x M2; b := M1-u; a := M0-u.
 - a Gamma-peel produces the corank charge det(Q_b Q_b^T)^{-a/2} (VALID only when Q_b Q_b^T is PosDef,
   i.e. rank Q_b = b), times a transverse "front loss" (E_top + E_tr)^{-q}, q=c'-ab/2.
 - E_top = ||P*Q_p + B12*Q_b||^2 (P invertible pivot on chart), E_tr = ||C*Qtilde_p*Pi_perp||^2,
   Pi_perp = I - Q_b^T (Q_b Q_b^T)^{-1} Q_b.
The design routes the deep-factor integrability via a DESCENT: the whole thing is dominated by
K * cornerComparator(redChain u M).integral(c'-ab/2), whose finiteness is the induction hypothesis on the
strictly shorter chain redChain u M (threshold reproduced by minAdm(M) <= ab + minAdm(redChain u M)).
The "corank Gram PosDef a.e." hypothesis (call it hGae) is discharged from: b <= rank Z_deep(z) a.e.,
which holds iff b <= deepTailMin(M) (generic product rank). There is an ALTERNATIVE mechanism (a "deep
stratum gate") that explicitly stratifies by the deep rank via a surviving-frame U_s with
Z Z^T >= eps^2 U_s U_s^T and reduces M2->m=min(M1,M_last)-j; the design claims this deep-stratum arc is
UNNECESSARY / off-path.

The per-stratum finiteness uses a banked radial blow-up requiring a degree-2-homogeneous transverse loss
g: R^C -> R (C=stratum codim) with hom: g(r w)=r^2 g(w), and a POSITIVE unit-sphere floor
hlb: for all ||w||=1, g(w) >= a > 0.
</task>

<questions>
Q-A (SOUNDNESS). Is the deep factor genuinely handled WITHOUT the explicit deep-stratum gate? Specifically:
 (a) The corank charge det(Q_b Q_b^T)^{-a/2}: does it integrate finitely via (hGae a.e. PosDef) + the front
     radial + the descent, or is there a deep rank-drop locus (Z_deep drops rank so Q_b Q_b^T singular for
     ALL A_cor) that makes hGae fail on POSITIVE measure and forces an explicit deep-stratum stratification?
 (b) Key sub-point: hGae needs b=M1-u <= deepTailMin(M) so that {z: rank Z_deep(z)<b} is measure zero. Does
     this hold at the cuts the peel actually uses? Reason about whether the peel being anchored at a BINDING
     cut t* (with shells j>=1, u=t*+j) forces b=M1-u < deepTailMin, versus a peel that would need arbitrary
     cuts. Is "a.e. PosDef (hGae)" ALONE enough to close the deep-factor INTEGRABILITY, or does the descent
     (IH on shorter chain) do the real work while hGae only enables the pointwise a.e. Gamma-peel?

Q-B (the hlb construction). For a single-block (ell,s) stratum, construct the transverse loss g on the C-dim
normal block after the unit-Jacobian Schur charts, and determine whether it is cleanly degree-2-homogeneous
with a positive unit-sphere floor.
 (i) Is g of the form g(w)=||Lambda w||^2 with Lambda a FIXED (chart-data-dependent) full-column-rank matrix
     built from the bounded spectators (pivot P, deep factor rows, C-coefficient)? If so, hom is exact and
     hlb=sigma_min(Lambda)^2. When is sigma_min(Lambda)>0, and what happens at chart boundaries?
 (ii) Is there a stratum whose transverse loss is NOT degree-2 (e.g. a biquadratic ||Y*W||^2 with BOTH Y and
      W transverse/blown-up), where the single-block homogeneity g(r w)=r^2 g(w) FAILS? Characterize it.
</questions>

<output_contract>
For each of Q-A(a),(b) and Q-B(i),(ii): give a decisive answer. Mark each claim [FACT] (exact algebra /
provable) vs [INFERENCE] (plausible). For Q-A: state clearly whether the explicit deep-stratum gate is
NECESSARY or UNNECESSARY, and WHY (what closes the deep-factor integrability). For Q-B: give the explicit g,
the hom check, the hlb proof (sigma_min), and precisely characterize the stratum (if any) where degree-2
homogeneity fails. Argue whichever way the mathematics actually goes; do not assume the design is correct.
</output_contract>

<grounding_rules>
Exact algebra only for [FACT]. The corank charge det(N G N^T)^{-a/2} over N (b x M2) with G=Z Z^T: its
A_cor-integral convergence and its leading singularity in G are standard Wishart/corank facts — state them.
Generic rank of a product of matrices = min of the widths. Do not paste code.
</grounding_rules>
