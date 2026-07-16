#!/usr/bin/env python3
"""
mixdegen_exact.py  --  EXACT-algebra adjudication of the b<j (Q_p-degeneration) regime.

Probe: M=(3,3,7), u=2, j=2, b=1 (so a=b=1, b<j).  L=0 leaf.
Everything here is exact-rational / integer arithmetic (Fraction / sympy).  NO floats are load-bearing.

Objects (read off incidence-cert §1/§3, thresholdhunt §1, shelljhunt §2):
 - Q_p = z  (u x M2 pivot block, free box at L=0),  Q_b = A_cor (b x M2 corank block, free box)
 - hsQ = (Q_p ; Q_b)  ((u+b) x M2 = M1 x M2)
 - front T = [P|B] (M0 x M1) plus C (transverse a rows).  Undecorated loss = frobSq(T . hsQ).
 - Decorated (post-shear, post Gamma=D integration) loss on the rank(Q_b)=b chart:
       F  =  ||H~||^2  +  ||Y . W||^2 ,   H~ in R^{u b},  Y=(P;C) in R^{M0 x u},  W = Q_p . N  (u x d), d=M2-b
   with weight det(Qb QbT)^{-a/2} = |detD|^{-a} det(I+XX^T)^{-a/2}, chart Jac |detD|^{d},
   exponent shift c' -> q = c' - a b /2.
"""
from fractions import Fraction as F

# ---------- chain data ----------
M0, M1, M2 = 3, 3, 7
u = 2
a = M0 - u          # 1
b = M1 - u          # 1
d = M2 - b          # 6
ab = a*b

def minAdm3(m0,m1,m2):
    # codim{B W = 0}, B m0xm1, W m1xm2, stratified by r=rank B
    return min((m0-r)*(m1-r)+r*m2 for r in range(0, min(m0,m1)+1))

minAdm = minAdm3(M0,M1,M2)
T1 = F(minAdm,2)
print(f"# M=({M0},{M1},{M2}) u={u} => a={a} b={b} d={d}  ab={ab}")
print(f"minAdm(M) = {minAdm}   T1 = minAdm/2 = {T1}   (brief claims T1=4.5)")
print(f"T1_q = T1 - ab/2 = {T1 - F(ab,2)}  (threshold of decorated obj in q = c'-ab/2)")

# argmin cut / shell structure
codims = {r:(M0-r)*(M1-r)+r*M2 for r in range(0,min(M0,M1)+1)}
tstar = min(codims, key=lambda r: codims[r])
r_range = min(M0-tstar, M1-tstar)
print(f"argmin t* = {tstar}  (codims {codims})   r=min(M0-t*,M1-t*)={r_range}")
print(f"cut u=t*+j => j = u - t* = {u-tstar};  b<j ?  {b} < {u-tstar} : {b < (u-tstar)}")

print("\n============ (1) POINTWISE inner-integral thresholds  I(W)=int_{H~,Y}(||H~||^2+||Y W||^2)^{-q} ============")
# for FIXED W of rank l:  ||Y W||^2 is a PSD form of rank M0*l in Y (in R^{M0 u}); H~ in R^{ub}.
# nondegenerate directions = ub + M0*l ; finite iff q < (ub + M0 l)/2.
ub = u*b
for l in range(0, u+1):
    thr_q  = F(ub + M0*l, 2)
    thr_cp = thr_q + F(ab,2)
    tag = ""
    if l == u:  tag = "  <- rank W=u : sigma_min(Qp)>0 generic"
    if l < u:   tag = f"  <- rank W={l}<u : sigma_min(Qp)->0 forced here"
    print(f"  rank W = l={l}:  I(W) finite iff q < {thr_q}  <=>  c' < {thr_cp}{tag}")
print("  (brief's '3' = the c'-threshold at rank W = 1 : above)")

print("\n============ (2) INTEGRATED off-shell decorated RLCT (joint int over H~,Y,W) ============")
# lambda(F) in q  =  mu + ub/2 ,  mu = RLCT(||Y W||^2), Y (M0 x u), W (u x d) = minAdm(M0,u,d)/2
mu_codim = minAdm3(M0, u, d)
mu = F(mu_codim, 2)
lam_q = mu + F(ub,2)
print(f"  mu = RLCT(||Y.W||^2) = minAdm({M0},{u},{d})/2 = {mu_codim}/2 = {mu}")
print(f"  lambda(F) in q = mu + ub/2 = {mu} + {F(ub,2)} = {lam_q}   => c'-threshold = {lam_q + F(ab,2)}")

print("\n============ (3) incidence-cert C_{l,s} table (cross-check min = 2*T1_q) ============")
def C_ls(l,s):
    return u*b + M0*l + (M0-s)*(u-l-s) + s*(d-l)
best = None
for l in range(0,u+1):
    for s in range(0,u+1):
        if l+s > u:          # need u-l-s >= 0 for the (M0-s)(u-l-s) block
            continue
        c = C_ls(l,s)
        print(f"  C_(l={l},s={s}) = {c}   -> q-thr {F(c,2)}  c'-thr {F(c,2)+F(ab,2)}")
        if best is None or c < best[0]:
            best = (c,l,s)
print(f"  MIN C_(l,s) = {best[0]} at (l,s)=({best[1]},{best[2]})   min/2 = {F(best[0],2)} = T1_q ? {F(best[0],2)==T1-F(ab,2)}")

print("\n============ (4) radial exponent of the Q_p-degeneration locus, INTEGRATED over W ============")
sv_weight = d - u                    # = 4
q_thr_rank1 = F(6 + sv_weight, 2)
print(f"  pointwise near rank-1 W:  I(W) ~ sigma_2^(5-2q)  (blows up q>5/2 i.e. c'>3) -- brief's pointwise fact")
print(f"  SV measure small-sigma weight (u x d, u<=d): sigma_2^(d-u) = sigma_2^{sv_weight} dsigma_2")
print(f"  int_0 sigma_2^(5-2q+{sv_weight}) dsigma_2 finite iff q < {q_thr_rank1}  <=> c' < {q_thr_rank1+F(ab,2)}")
print(f"  => rank-1-W (sigma_min(Qp)->0) locus INTEGRATED converges to q<{q_thr_rank1} (c'<{q_thr_rank1+F(ab,2)}),")
print(f"     ABOVE the binding q<{lam_q} (c'<{lam_q+F(ab,2)}=T1). So it is NOT the binding stratum.")

print("\n============ (5) the BINDING stratum: front vanish {Y=0,H~=0} at GENERIC (full-rank) W ============")
q_front = F(ub + M0*u, 2)
print(f"  front-vanish at generic W: q < (ub+M0*u)/2 = {q_front}  <=> c' < {q_front+F(ab,2)} = T1")
print(f"  equals T1, realized on codim-0 (generic) W => BINDING. Matches lambda(F)={lam_q}.")

print("\n============ (6) subset-monotonicity (rigorous general no-go against the drop) ============")
print("  G_shell = int_{shell-j subset} (detGram)*I(W)  <=  int_{full box} (detGram)*I(W) = G_offshell")
print(f"  G_offshell finite for c' < {lam_q+F(ab,2)} = T1.  Same nonneg integrand, shell domain SUBSET")
print(f"  => RLCT(G_shell) >= RLCT(G_offshell) = T1 = {T1}.  NO drop to 3.")
