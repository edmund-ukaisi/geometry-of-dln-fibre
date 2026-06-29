import sympy as sp

# L=2 smeared: r = deepRank = min(M0, M1) (front-bottleneck, certificate sec 1).
# smeared requires s = M1 - r > 0.
# Enumerate (M0, M1) and derive r, s, and P1 shape.
print("L=2 front-bottleneck r = min(M0,M1); smeared needs s=M1-r>0:")
print(f"{'M0':>3}{'M1':>3}{'r=min':>6}{'s=M1-r':>7}{'P1 shape':>10}{'smeared?':>9}{'P1 type':>9}")
for M0 in range(1,6):
    for M1 in range(1,6):
        r = min(M0,M1)
        s = M1 - r
        smeared = s > 0
        if r == M0 and r == M1: typ="square"
        elif r == M0: typ="square"   # r=M0<=M1
        elif r == M1: typ="(s=0)"
        ptype = "SQUARE" if r==M0 else ("WIDE" if r>M0 else "TALL")
        if smeared:
            print(f"{M0:>3}{M1:>3}{r:>6}{s:>7}{f'{M0}x{r}':>10}{'YES':>9}{ptype:>9}")
print()
print("CONCLUSION: every L=2 smeared (s>0) case has r=min(M0,M1)=M0 (since s>0 forces M1>r,")
print("and r=min(M0,M1); if r=M1 then s=0; so r=M0 and M0<M1). Hence P1 is M0 x M0 = SQUARE.")
print()
# Verify the cancellation holds for free A0 in every smeared L=2 case (r = M0 square):
import random
print("Exact-rational cancellation check, free A0, r=M0 (square), several smeared (M0<M1):")
for (M0,M1) in [(1,2),(2,3),(2,4),(3,4),(1,3),(2,5),(3,5)]:
    r = M0; s = M1-r
    random.seed(999+M0*10+M1)
    A = sp.Matrix(M0,M1, lambda i,j: sp.Rational(random.randint(1,9), random.randint(1,4)))
    P1=A[:,:r]; P2=A[:,r:]
    G=P1.T*P1; dG=G.det()
    if dG==0:
        print(f"  ({M0},{M1},r={r}): SKIP det0"); continue
    Lam0=G.inv()*P1.T*P2
    resid=sp.simplify(P1*Lam0-P2)
    print(f"  ({M0},{M1}) r={r} s={s}: P1 {M0}x{r} square, detG={dG}!=0, P1*Lam0==P2 ? {resid.is_zero_matrix}")
